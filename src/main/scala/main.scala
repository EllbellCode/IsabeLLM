import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
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

case class TestResult(runId: Int, success: Boolean, iterations: Int, sledgehammerUsed: Boolean)

object isabellm {

  // Global State
  val stateCache = mutable.TreeMap[Int, ToplevelState]()
  val jsonPaths = mutable.Map[String, String]()
  val traceBuffer = mutable.Map[String, ArrayBuffer[String]]()
  val testResults = ArrayBuffer[TestResult]()
  
  // Configuration
  val totalTestRuns = 1     
  val maxTestIters = 3       

  // Session Variables 
  var iter = 0
  var done = false
  var sledgehammerUsedInRun = false 
  var pendingProof: Option[(String, String, String)] = None
  var preservedError: Option[String] = None
  var preservedLine: Option[String] = None

  def logTrace(lemmaName: String, message: String): Unit = {
      traceBuffer.getOrElseUpdate(lemmaName, ArrayBuffer()) += message
  }

  def getAndClearTrace(lemmaName: String): String = {
      val trace = traceBuffer.get(lemmaName).map(_.mkString("\n")).getOrElse("")
      traceBuffer.remove(lemmaName)
      trace
  }

  def logErrorAndAction(name: String, line: String, error: String, action: String): Unit = {
    val cleanError = error.linesIterator.take(3).mkString(" ").trim 
    val cleanLine = line.trim
    val entry = s"""
    |   [Step Failed]
    |   Code: "$cleanLine"
    |   Error: $cleanError
    |   Automated Action: $action
    """.stripMargin.trim
    logTrace(name, entry)
  }

  def main(args: Array[String]): Unit = {
    println("***************************************************")
    val isabelleHome = Paths.get("/home/eaj123/PhDLinux/Isabellm/Isabelle2025")
    val wd = "/home/eaj123/PhDLinux/Isabellm/Test"
    val theoryPath = "/home/eaj123/PhDLinux/Isabellm/Test/test.thy"

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

    val originalTheoryContent = extractText(theoryPath)
    println(s"💾 Original theory content loaded (${originalTheoryContent.length} chars).")

    try {
        for (run <- 1 to totalTestRuns) {
            println(s"\n\n🔴🔴🔴 STARTING TEST RUN $run / $totalTestRuns 🔴🔴🔴")
            
            println("♻️  Restoring theory file to original state...")
            injectAll(theoryPath, originalTheoryContent)

            resetSessionState()

            // FIX 1: Removed 'isabelle' from the explicit arguments. 
            // Since it is marked 'implicit' in main scope, it is passed automatically.
            val result = runTestingSession(run, service, theoryPath, isabelleHome, wd)
            
            testResults.append(result)
            
            println(s"🏁 Run $run Result: Success=${result.success}, Iters=${result.iterations}, Hammer=${result.sledgehammerUsed}")
        }

    } finally {
        println("🧹 Final cleanup: Restoring original file...")
        injectAll(theoryPath, originalTheoryContent)
        isabelle.destroy()
        printSummary()
    }
  }

  def resetSessionState(): Unit = {
      iter = 0
      done = false
      sledgehammerUsedInRun = false
      stateCache.clear()
      traceBuffer.clear()
      pendingProof = None
      preservedError = None
      preservedLine = None
  }
  
  def printSummary(): Unit = {
      println("\n" + "="*50)
      println(f"${"Run"}%-5s | ${"Success"}%-10s | ${"LLM Iters"}%-10s | ${"Sledgehammer"}%-15s")
      println("-" * 50)
      
      var successes = 0
      testResults.foreach { r =>
          if (r.success) successes += 1
          val hammerStr = if (r.sledgehammerUsed) "YES" else "NO"
          val successStr = if (r.success) "✅ YES" else "❌ NO"
          println(f"${r.runId}%-5d | $successStr%-10s | ${r.iterations}%-10d | $hammerStr%-15s")
      }
      println("-" * 50)
      println(s"Total Success Rate: $successes / $totalTestRuns")
      println("="*50 + "\n")
  }

  // FIX 2: Moved 'implicit isabelle' to a separate parameter list at the end (Currying)
  def runTestingSession(runId: Int, service: SledgehammerService, theoryPath: String, isabelleHome: java.nio.file.Path, wd: String)(implicit isabelle: Isabelle): TestResult = {
      
      var success = false

      while (iter < maxTestIters && !done) {
        println(s"--- Run $runId: Iteration ${iter + 1} of $maxTestIters ---")
        
        val theoryText = extractText(theoryPath)
        val replacedText = llm.llmOutput.replaceUnicode(theoryText)
        injectAll(theoryPath, replacedText)

        val fileVerify = scala.io.Source.fromFile(theoryPath)
        val lineCount = try fileVerify.getLines().size finally fileVerify.close()
        if (lineCount <= 1 && replacedText.contains("\n")) {
           Thread.sleep(500)
        }

        val theoryManager = new TheoryManager(path_to_isa_bin = isabelleHome.toString, wd = wd)
        val theorySource = TheoryManager.Text(replacedText, Paths.get(theoryPath).toAbsolutePath)
        
        val thy = theoryManager.beginTheory(theorySource)
        val transitions = service.parse_text(thy, replacedText).force.retrieveNow
        
        var currentToplevel = service.init_toplevel().force.retrieveNow

        var currentLine = 1
        var lastIndex = 0
        var errorFoundInSession = false

        breakable {
          for (((transition, rawText), index) <- transitions.zipWithIndex) {
            val trimmedText = rawText.trim

            val matchIndex = replacedText.indexOf(rawText, lastIndex)
            if (matchIndex != -1) {
                val gap = replacedText.substring(lastIndex, matchIndex)
                currentLine += gap.count(_ == '\n')
                lastIndex = matchIndex 
            }
            
            if (trimmedText == "sorry" || trimmedText.startsWith("sorry ")) {
                println(s"Found 'sorry' at line $currentLine. Initialising IsabeLLM...")
                val solved = processError("quick_and_dirty", currentLine, theoryPath, thy, currentToplevel, service)
               
                if (solved) {
                    stateCache.clear() 
                    errorFoundInSession = true
                    break()
                }
            }

            try {
              if (!stateCache.contains(index)) {
                val executionFuture = Future {
                    service.command_exception(true, transition, currentToplevel).force.retrieveNow
                }
                currentToplevel = Await.result(executionFuture, 30.seconds) 
                stateCache(index) = currentToplevel
              } else {
                currentToplevel = stateCache(index)
              }
            } catch {
              case _: TimeoutException => 
                println(s"⏳ Timeout/Stall detected at line $currentLine.")
                errorFoundInSession = true
                val solved = processError("Timeout", currentLine, theoryPath, thy, currentToplevel, service)
                if (solved) {
                  stateCache.clear()
                  println("✅ Timeout resolved. Cache cleared. Restarting...")
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
                  stateCache.clear()
                  println(s"✅ Fix applied. Cache cleared. Restarting...") 
                  break()
                } else {
                  done = true 
                  break()
                }
            }
            
            if (matchIndex != -1) {
                currentLine += rawText.count(_ == '\n')
                lastIndex += rawText.length
            } else {
                currentLine += rawText.count(_ == '\n')
            }
          }
        }

        if (!errorFoundInSession) {
          println("✅ .thy file verified successfully.")
          success = true
          
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
      
      TestResult(runId, success, iter, sledgehammerUsedInRun)
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

    def invokeLLM(): Unit = {
      
      val (errorToPass, lineToPass) = (preservedError, preservedLine) match {
        case (Some(prevErr), Some(prevLine)) => (prevErr, prevLine)
        case _ => (isabelleErrors, lineContent)
      }
      val errorTrace = getAndClearTrace(name)

      var retryCount = 0
      val maxRetries = 3
      var success = false

      while (!success && !done && retryCount < maxRetries) {
          try {
              if (retryCount > 0) println(s"   -> Retry Attempt ${retryCount + 1}...")
              else println(s"Calling LLM for lemma '$name'...")

              val generatedProof = llm.llmOutput.callLLM(
                utils.extract.extractThy(filePath, safeLineNum), 
                if (safeLineNum <= maxLines) extractAll(filePath, safeLineNum) else "File truncated", 
                currentStatement, 
                errorToPass, 
                lineToPass, 
                json_path,
                filePath,
                safeLineNum,
                errorTrace
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
                
                iter += 1
                preservedError = None 
                preservedLine = None
                success = true
                
              } else {
                println("⚠️ LLM returned empty output. Retrying immediately...")
                retryCount += 1
              }

          } catch {
              case e: Exception =>
                println(s"CRITICAL: LLM Service failed: ${e.getMessage}")
                retryCount += 1
          }
      }

      if (!success) {
          println("❌ LLM failed to produce output after max retries. Stopping session.")
          done = true
      }
    }

    if (isabelleErrors.contains("quick_and_dirty")) {
      invokeLLM()
      return true
    }

    if (isabelleErrors.contains("Failed to finish proof") || 
        isabelleErrors.contains("Failed to apply initial proof method") ||
        isabelleErrors.contains("Malformed command syntax") ||
        isabelleErrors.contains("Illegal application of proof command")) { 
      
      if (isabelleErrors.contains("No subgoals!")) {
        println("No subgoals detected! Cleaning up line...")
        logErrorAndAction(name, lineContent, isabelleErrors, "Removed completed proof step (No subgoals).")
        injectLine(filePath, safeLineNum, "")
        return true
      }

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

      if (localeFix(filePath, name)) {
          logErrorAndAction(name, "locale ...", isabelleErrors, "Injected missing locale assumptions.")
          return true
      }
      if (assmsFix(filePath, name)) {
          logErrorAndAction(name, "using assms", isabelleErrors, "Injected missing 'using assms'.")
          return true
      }

      println(s"Running Sledgehammer (targeting line $targetLine)...")
      val result = service.call_sledgehammer(currentState, thy)
      val targetText = if (targetLine <= maxLines) fileLines(targetLine - 1) else ""
      
      if (result._1 && result._2._2.nonEmpty) {
          val proof = service.extractProof(result._2._2.head)
          println(s"Sledgehammer success: $proof")
          injectProof(filePath, targetLine, proof) 
          pendingProof = Some((filePath, currentStatement, proof))
          
          sledgehammerUsedInRun = true 
          
          return true
      } else {
          println("Sledgehammer failed. Delegating to LLM...")
          logErrorAndAction(name, targetText, isabelleErrors, "Sledgehammer failed to find a proof. Injected 'sorry'.")
          
          injectProof(filePath, targetLine, "sorry") 
          preservedError = Some(isabelleErrors) 
          preservedLine = Some(lineContent)
          invokeLLM()
          return true
      }
    }
    
    if (isabelleErrors.contains("Timeout")) {
       println("Timeout detected. Attempting fixes...")
       
       val currentLineIndex = safeLineNum - 1
       val currentLineText = if (currentLineIndex >= 0 && currentLineIndex < maxLines) fileLines(currentLineIndex) else ""
       val isStuckOnTactic = utils.timeout.tacticKeywords.exists(kw => 
           currentLineText.toLowerCase.contains(kw) && !currentLineText.contains("(*SAFE*)")
       )
       
       val targetLine = if (isStuckOnTactic) safeLineNum else {
           val (start, end) = utils.timeout.findLines(filePath, name)
           val tactic_line = utils.timeout.tacticSearch(filePath, start, end)
           if (tactic_line != -1) tactic_line + 1 else safeLineNum
       }
       
       val targetLineText = if (targetLine <= maxLines) fileLines(targetLine - 1) else "EOF"

       val result = service.call_sledgehammer(currentState, thy)
       
       if (result._1 && result._2._2.nonEmpty) {
         val proof = service.extractProof(result._2._2.head)
         val finalProof = if (proof.contains("by")) proof + " (*SAFE*)" else proof
         utils.inject.injectProof(filePath, targetLine, finalProof)
         
         sledgehammerUsedInRun = true 
         
         return true
       } else {
          println("Sledgehammer failed on timeout. Injecting sorry...")
          
          logErrorAndAction(name, targetLineText, isabelleErrors, "Timeout detected. Sledgehammer failed to resolve tactic. Injected 'sorry'.")
          
          utils.inject.injectProof(filePath, targetLine, "sorry")
          preservedError = Some("Timeout")
          preservedLine = Some(if (targetLine <= maxLines) fileLines(targetLine - 1) else "")
          invokeLLM()
          return true
       }
    }

    if (isabelleErrors.contains("Undefined")) {
       println("Undefined fact detected...")
       val undef = extractUndefined(isabelleErrors)
       
       logErrorAndAction(name, lineContent, isabelleErrors, s"Fixed undefined fact/method '$undef'.")
       
       processUndefined(filePath, safeLineNum, undef)
       return true
    }

    if (isabelleErrors.contains("exception THM 0 raised")) {
       println("THM 0 error. Removing offending theorem usage...")
       logErrorAndAction(name, lineContent, isabelleErrors, "Removed invalid THM 0 usage.")
       injectLine(filePath, safeLineNum, removeTHM0(lineContent))
       return true
    }
    
    if (isabelleErrors.contains("Bad context")) {
       println("Bad Context. removing line...")
       logErrorAndAction(name, lineContent, isabelleErrors, "Removed bad context line.")
       injectLine(filePath, safeLineNum, "")
       return true
    }

    if (isabelleErrors.contains("Inner lexical error")) {
       if (containsUnicode(isabelleErrors)) {
          println("Unicode error detected. Normalizing file...")
          logErrorAndAction(name, lineContent, isabelleErrors, "Normalized Unicode characters.")
          injectAll(filePath, replaceUnicode(extractText(filePath)))
          return true
       }
       println("Lexical error (non-unicode). Sending to LLM...")
       invokeLLM()
       return true
    }

    println("Alternative error detected. Sending to LLM...")
    invokeLLM()
    true
  }
}