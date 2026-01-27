import scala.collection.mutable
import java.nio.file.{Paths, Files}
import java.io.File
import scala.concurrent.{Future, Await}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import java.util.concurrent.TimeoutException
import scala.util.control.Breaks.{break, breakable} 
import scala.sys.process._
import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.{Theory, ToplevelState, Transition => IsaTransition}
import de.unruh.isabelle.mlvalue.Implicits._ 
import de.unruh.isabelle.pure.Implicits._

// Utility Imports
import utils.extract._
import utils.inject._
import utils.undefined._
import utils.timeout._
import llm.llmOutput._ 
import llm.history._
import sledgehammer.SledgehammerService
import sledgehammer.TheoryManager

object isabellm {

  val stateCache = mutable.TreeMap[Int, ToplevelState]()
  val jsonPaths = mutable.Map[String, String]()
  val maxIters = 10 
  var iter = 0
  var done = false

  var pendingProof: Option[(String, String, String)] = None

  var preservedError: Option[String] = None
  var preservedLine: Option[String] = None

  def main(args: Array[String]): Unit = {
    println("***************************************************")
    // Ensure these paths match your actual installation
    val isabelleHome = Paths.get("/home/eaj123/PhDLinux/Isabellm/Isabelle2025")
    val wd = "/home/eaj123/PhDLinux/Isabellm/Test"

    println("Initialising Isabelle 2025...")
    
    val setup = Isabelle.Setup(
        isabelleHome = isabelleHome, 
        logic = "HOL",
        sessionRoots = Nil, 
        userDir = None,
        workingDirectory = Paths.get(wd),
        build = false,
        verbose = false 
    )
    implicit val isabelle: Isabelle = new Isabelle(setup)

    println("Initialising Sledgehammer Service...")
    val service = new SledgehammerService()
    val theoryPath = "/home/eaj123/PhDLinux/Isabellm/Test/test.thy"

    try {
      while (iter < maxIters && !done) {
        println(s"--- Iteration ${iter + 1} of $maxIters ---")
        
        // 1. Unicode Normalization & Injection
        val theoryText = extractText(theoryPath)
        val replacedText = llm.llmOutput.replaceUnicode(theoryText)
        injectAll(theoryPath, replacedText)

        // Sync check
        val fileVerify = scala.io.Source.fromFile(theoryPath)
        val lineCount = try fileVerify.getLines().size finally fileVerify.close()
        if (lineCount <= 1 && replacedText.contains("\n")) {
           println("⚠️ Warning: File system sync delay detected. Waiting...")
           Thread.sleep(500)
        }

        val theoryManager = new TheoryManager(path_to_isa_bin = isabelleHome.toString, wd = wd)
        val theorySource = TheoryManager.Text(replacedText, Paths.get(theoryPath).toAbsolutePath)
        
        // Start Theory Processing
        val thy = theoryManager.beginTheory(theorySource)
        val transitions = service.parse_text(thy, replacedText).force.retrieveNow
        println(s"ℹ️  Found ${transitions.length} transitions to process.")

        var currentToplevel = service.init_toplevel().force.retrieveNow

        // NEW: Accurate Position Tracking Variables
        var currentLine = 1
        var lastIndex = 0
        
        var errorFoundInSession = false

        breakable {
          for (((transition, rawText), index) <- transitions.zipWithIndex) {
            val trimmedText = rawText.trim

            // 1. Calculate precise line number by finding rawText in the file
            // This accounts for gaps (comments/newlines) that the previous logic missed
            val matchIndex = replacedText.indexOf(rawText, lastIndex)
            if (matchIndex != -1) {
                // Count newlines in the gap between the last command and this one
                val gap = replacedText.substring(lastIndex, matchIndex)
                currentLine += gap.count(_ == '\n')
                lastIndex = matchIndex // Move pointer to start of this command
            }
            
            // Check for explicit "sorry"
            if (trimmedText == "sorry" || trimmedText.startsWith("sorry ")) {
                println(s"Found 'sorry' at line $currentLine. Initialising IsabeLLM...")
                val solved = processError("quick_and_dirty", currentLine, theoryPath, thy, currentToplevel, service)
               
                if (solved) {
                    stateCache.keys.filter(_ >= index).foreach(stateCache.remove)
                    errorFoundInSession = true
                    break()
                }
            }

            try {
              if (!stateCache.contains(index)) {
                // Wrap blocking call in Future
                val executionFuture = Future {
                    service.command_exception(true, transition, currentToplevel).force.retrieveNow
                }
                
                // 2. Main thread waits here with the timer
                currentToplevel = Await.result(executionFuture, 30.seconds) 
                
                stateCache(index) = currentToplevel
              } else {
                currentToplevel = stateCache(index)
              }
            } catch {
              // 3. Catch the explicit Timeout
              case _: TimeoutException => 
                println(s"⏳ Timeout/Stall detected at line $currentLine.")
                errorFoundInSession = true
                
                // Manually trigger the "Timeout" logic in processError
                val solved = processError("Timeout", currentLine, theoryPath, thy, currentToplevel, service)
                
                if (solved) {
                  println("✅ Timeout resolved. Cleaning cache...")
                  stateCache.keys.filter(_ >= index).foreach(stateCache.remove)
                  break()
                } else {
                  done = true
                  break()
                }

              case e: Exception =>
                errorFoundInSession = true
                val errorMsg = e.getMessage
                println(s"⚠️ Error at line $currentLine: $errorMsg")
                
                val solved = processError(errorMsg, currentLine, theoryPath, thy, currentToplevel, service)
                
                if (solved) {
                  println(s"✅ Fix applied. Clearing cache from index $index onwards...")
                  stateCache.keys.filter(_ >= index).foreach(stateCache.remove)
                  break() 
                } else {
                  println("❌ No automated fix found. Stopping session.")
                  done = true 
                  break()
                }
            }
            
            // Advance the line counter past the current command
            if (matchIndex != -1) {
                currentLine += rawText.count(_ == '\n')
                lastIndex += rawText.length
            } else {
                // Fallback if indexOf failed (unlikely)
                currentLine += rawText.count(_ == '\n')
            }
          }
        }

        if (!errorFoundInSession) {
          println("✅ .thy file verified successfully.")

          if (pendingProof.isDefined) {
              val (fPath, lemma, code) = pendingProof.get
              println(s"💾 Saving successful proof for '$lemma' to memory...")
              
              val scriptPath = "/home/eaj123/PhDLinux/Isabellm/Test/src/main/python/send_to_llm.py"
              val cmd = Seq("python3", scriptPath, "store", fPath, lemma, code)
              cmd.!
              
              pendingProof = None 
          }

          done = true
        }
      }
    } finally {
      isabelle.destroy()
    }
    println(s"Exiting after $iter LLM iteration(s).")
  }
  
  def processError(
    isabelleErrors: String, lineNum: Int, filePath: String, 
    thy: Theory, currentState: ToplevelState, service: SledgehammerService
  )(implicit isabelle: Isabelle): Boolean = {
    
    val source = scala.io.Source.fromFile(filePath)
    val fileLines = try source.getLines().toVector finally source.close()
    val maxLines = fileLines.size
    val safeLineNum = if (lineNum > maxLines) maxLines else if (lineNum < 1) 1 else lineNum

    val currentStatement = try { extractStatement(filePath, safeLineNum) } catch { case _: Exception => "undefined" }
    val name = extractName(currentStatement)
    val lineContent = if (safeLineNum <= maxLines) fileLines(safeLineNum - 1) else ""
    
    val json_path = jsonPaths.getOrElseUpdate(name, {
      val freshPath = getUniqueJsonPath("history", name)
      jsonCreate(new File(freshPath).getName.stripSuffix(".json"))
      freshPath
    })

    // Inner helper to handle LLM calls
    def invokeLLM(): Unit = {
      try {
          val (errorToPass, lineToPass) = (preservedError, preservedLine) match {
            case (Some(prevErr), Some(prevLine)) => 
              preservedError = None 
              preservedLine = None
              (prevErr, prevLine)
            case _ => (isabelleErrors, lineContent)
          }

          println(s"Calling LLM for lemma '$name'...")
          
          val generatedProof = llm.llmOutput.callLLM(
            utils.extract.extractThy(filePath, safeLineNum), 
            if (safeLineNum <= maxLines) extractAll(filePath, safeLineNum) else "File truncated", 
            currentStatement, 
            errorToPass, 
            lineToPass, 
            json_path,
            filePath,
            safeLineNum 
          )
          
          if (generatedProof.isDefined) {
            val code = generatedProof.get.trim
  
            val isFullBlock = Set("lemma", "theorem", "proposition", "corollary").exists(kw => code.startsWith(kw))

            if (isFullBlock) {
                println("LLM returned full block. Replacing existing block...")
                utils.inject.injectLemma(code, filePath, safeLineNum)
            } else {
                println("LLM returned proof snippet. Injecting into line...")
                utils.inject.injectProof(filePath, safeLineNum, code)
            }

            pendingProof = Some((filePath, currentStatement, code))
          } else {

            println("❌ No proof generated by LLM. Stopping session.")
            done = true
          }

          iter += 1
      } catch {
          case e: Exception =>
            println(s"CRITICAL: LLM Service failed: ${e.getMessage}")
            done = true 
      }
    }

    // --- ERROR HANDLING DECISION TREE ---

    // 1. SORRY / Quick & Dirty
    if (isabelleErrors.contains("quick_and_dirty")) {
      invokeLLM()
      return true
    }

    // 2. Proof Failures
    if (isabelleErrors.contains("Failed to finish proof") || 
        isabelleErrors.contains("Failed to apply initial proof method") ||
        isabelleErrors.contains("Malformed command syntax") ||
        isabelleErrors.contains("Illegal application of proof command")) { 
      
      // A. No subgoals -> Clean up
      if (isabelleErrors.contains("No subgoals!")) {
        println("No subgoals detected! Cleaning up line...")
        injectLine(filePath, safeLineNum, "")
        return true
      }

      // B. Smart Targeting: Handle split-line proofs
      var targetLine = safeLineNum
      if (safeLineNum < maxLines) {
          val currentLine = fileLines(safeLineNum - 1).trim 
          val nextLine = fileLines(safeLineNum).trim        
          
          val nextIsProof = nextLine.startsWith("by") || nextLine.startsWith("apply")
          val currentIsProof = currentLine.startsWith("by") || currentLine.startsWith("apply") || currentLine.endsWith("by")

          if (nextIsProof && !currentIsProof) {
              println(s"Proof method detected on next line (Line ${safeLineNum + 1}). Adjusting target...")
              targetLine = safeLineNum + 1
          }
      }

      // C. Structure Fixes (Run BEFORE Sledgehammer)
      if (localeFix(filePath, name)) return true
      if (assmsFix(filePath, name)) return true

      // D. Sledgehammer (Using targetLine)
      println(s"Running Sledgehammer (targeting line $targetLine)...")
      val result = service.call_sledgehammer(currentState, thy)
      
      if (result._1 && result._2._2.nonEmpty) {
          val proof = service.extractProof(result._2._2.head)
          println(s"Sledgehammer success: $proof")
          injectProof(filePath, targetLine, proof) 
          pendingProof = Some((filePath, currentStatement, proof))
          return true
      } else {
          // E. Fallback to LLM
          println("Sledgehammer failed. Delegating to LLM...")
          injectProof(filePath, targetLine, "sorry") 
          preservedError = Some(isabelleErrors) 
          preservedLine = Some(lineContent)
          invokeLLM()
          return true
      }
    }
    
    // 3. Timeouts
    if (isabelleErrors.contains("Timeout")) {
       println("Timeout detected. Attempting fixes...")
       
       // STEP 1: Precision Targeting
       // Check if the specific line where it stalled contains a tactic keyword.
       // If yes, target IT, do not scan from the start of the lemma.
       val currentLineIndex = safeLineNum - 1
       val currentLineText = if (currentLineIndex >= 0 && currentLineIndex < maxLines) fileLines(currentLineIndex) else ""
       
       // Note: utils.timeout.tacticKeywords is Set("blast", "metis", "auto")
       val isStuckOnTactic = utils.timeout.tacticKeywords.exists(kw => 
           currentLineText.toLowerCase.contains(kw) && !currentLineText.contains("(*SAFE*)")
       )
       
       val targetLine = if (isStuckOnTactic) {
           println(s"Targeting stuck tactic at line $safeLineNum: '${currentLineText.trim}'")
           safeLineNum
       } else {
           // STEP 2: Fallback Search (Old Behavior)
           // If the timeout line doesn't look like a tactic (e.g. stalled on 'qed' or whitespace),
           // search the lemma for the first potential culprit.
           println(s"Line $safeLineNum isn't a recognized tactic. Scanning lemma for candidates...")
           val (start, end) = utils.timeout.findLines(filePath, name)
           val tactic_line = utils.timeout.tacticSearch(filePath, start, end)
           
           if (tactic_line != -1) tactic_line + 1 else safeLineNum
       }
       
       println(s"Hammering tactic at line $targetLine...")
       
       // Priority 2: Sledgehammer the specific line
       val result = service.call_sledgehammer(currentState, thy)
       
       if (result._1 && result._2._2.nonEmpty) {
         val proof = service.extractProof(result._2._2.head)
         val finalProof = if (proof.contains("by")) proof + " (*SAFE*)" else proof
         utils.inject.injectProof(filePath, targetLine, finalProof)
         return true
       } else {
          // Priority 3: Fail to LLM 
          println("Sledgehammer failed on timeout. Injecting sorry...")
          utils.inject.injectProof(filePath, targetLine, "sorry")
          preservedError = Some("Timeout")
          // Ensure we extract the line content from the TARGET line, not necessarily the error line
          preservedLine = Some(if (targetLine <= maxLines) fileLines(targetLine - 1) else "")
          invokeLLM()
          return true
       }
    }

    // 4. Undefined Facts
    if (isabelleErrors.contains("Undefined")) {
       println("Undefined fact detected...")
       processUndefined(filePath, safeLineNum, extractUndefined(isabelleErrors))
       return true
    }

    // 5. Context Errors (THM 0, Bad Context)
    if (isabelleErrors.contains("exception THM 0 raised")) {
       println("THM 0 error. Removing offending theorem usage...")
       injectLine(filePath, safeLineNum, removeTHM0(lineContent))
       return true
    }
    
    if (isabelleErrors.contains("Bad context")) {
       println("Bad Context. removing line...")
       injectLine(filePath, safeLineNum, "")
       return true
    }

    // 6. Lexical/Unicode Errors
    if (isabelleErrors.contains("Inner lexical error")) {
       if (containsUnicode(isabelleErrors)) {
          println("Unicode error detected. Normalizing file...")
          injectAll(filePath, replaceUnicode(extractText(filePath)))
          return true
       }
       println("Lexical error (non-unicode). Sending to LLM...")
       invokeLLM()
       return true
    }

    // 7. Fallback
    println("Alternative error detected. Sending to LLM...")
    invokeLLM()
    true
  }
}