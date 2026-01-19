
import scala.collection.mutable
import java.nio.file.{Paths, Files}
import java.io.File
import scala.concurrent.{Future, Await}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import java.util.concurrent.TimeoutException
import scala.util.control.Breaks.{break, breakable} 

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
  val maxIters = 3
  var iter = 0
  var done = false

  var preservedError: Option[String] = None
  var preservedLine: Option[String] = None

  def main(args: Array[String]): Unit = {
    println("***************************************************")
    val isabelleHome = Paths.get("/home/eaj123/PhDLinux/Isabellm/Isabelle2025")
    val wd = "/home/eaj123/PhDLinux/Isabellm/Test"

    println("Initialising Isabelle...")
    
    // CONFIGURATION FROM YOUR OLD WORKING CODE
    // 1. sessionRoots = Nil (Prevents loading local ROOT files)
    // 2. userDir = None (Prevents loading user-specific settings)
    // 3. build = false (Prevents auto-build timeouts/errors)
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
        println(s"--- Iteration ${iter + 1} ---")
        
        val theoryText = extractText(theoryPath)
        val replacedText = llm.llmOutput.replaceUnicode(theoryText)
        injectAll(theoryPath, replacedText)

        val fileVerify = scala.io.Source.fromFile(theoryPath)
        val lineCount = try fileVerify.getLines().size finally fileVerify.close()
        if (lineCount <= 1 && replacedText.contains("\n")) {
           println("⚠️ Warning: File system sync delay detected. Waiting...")
           Thread.sleep(500)
        }

        val theoryManager = new TheoryManager(path_to_isa_bin = isabelleHome.toString, wd = wd)
        val theorySource = TheoryManager.Text(replacedText, Paths.get(theoryPath).toAbsolutePath)
        val thy = theoryManager.beginTheory(theorySource)
        
        val transitions = service.parse_text(thy, replacedText).force.retrieveNow
        var currentToplevel = service.init_toplevel().force.retrieveNow
        
        var currentLine = 1
        var errorFoundInSession = false

        breakable {
          for (((transition, rawText), index) <- transitions.zipWithIndex) {
            val trimmedText = rawText.trim
            
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
                currentToplevel = service.command_exception(true, transition, currentToplevel).force.retrieveNow
                stateCache(index) = currentToplevel
              } else {
                currentToplevel = stateCache(index)
              }
            } catch {
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
            
            currentLine += rawText.count(_ == '\n')
          }
        }

        if (!errorFoundInSession) {
          println("✅ .thy file verified successfully.")
          done = true
        }
      }
    } finally {
      isabelle.destroy()
    }
    println(s"Exiting after $iter LLM iteration(s).")
  }
  
  // (Helper function processError remains unchanged)
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
      try {
          val (errorToPass, lineToPass) = (preservedError, preservedLine) match {
            case (Some(prevErr), Some(prevLine)) => 
              preservedError = None 
              preservedLine = None
              (prevErr, prevLine)
            case _ => (isabelleErrors, lineContent)
          }

          println(s"Calling LLM...")
          llm.llmOutput.callLLM(
            utils.extract.extractThy(filePath, safeLineNum), 
            if (safeLineNum <= maxLines) extractAll(filePath, safeLineNum) else "File truncated", 
            currentStatement, 
            errorToPass, 
            lineToPass, 
            json_path,
            filePath,
            safeLineNum 
          )
          iter += 1
      } catch {
          case e: Exception =>
            println(s"CRITICAL: LLM Service failed: ${e.getMessage}")
            done = true 
      }
    }

    if (isabelleErrors.contains("quick_and_dirty")) {
      invokeLLM()
      return true
    }

    if (isabelleErrors.contains("Failed to finish proof") || 
        isabelleErrors.contains("Failed to apply initial proof method") ||
        isabelleErrors.contains("Malformed command syntax")) {
      
      if (isabelleErrors.contains("No subgoals!")) {
        injectLine(filePath, safeLineNum, "")
        return true
      }

      if (localeFix(filePath, name)) return true
      if (assmsFix(filePath, name)) return true

      println("Running Sledgehammer...")
      val result = service.call_sledgehammer(currentState, thy)
      if (result._1 && result._2._2.nonEmpty) {
          val proof = service.extractProof(result._2._2.head)
          println(proof)
          injectProof(filePath, safeLineNum, proof)
          return true
      } else {
          injectProof(filePath, safeLineNum, "sorry")
          preservedError = Some(isabelleErrors) 
          preservedLine = Some(lineContent)
          invokeLLM()
          return true
      }
    } 

    if (isabelleErrors.toLowerCase.contains("timeout")) {
       val (start, end) = findLines(filePath, name)
       val tactic_line = tacticSearch(filePath, start, end) + 1
       val (success, (_, solution)) = service.call_sledgehammer(currentState, thy)
       if (success) {
         val proof = service.extractProof(solution.head)
         injectProof(filePath, tactic_line, if (proof.contains("by")) proof + "(*SAFE*)" else proof)
         return true
       } else {
          injectProof(filePath, tactic_line, "sorry")
          preservedError = Some("Timeout")
          preservedLine = Some(extractLine(filePath, tactic_line))
          invokeLLM()
          return true
       }
    }

    if (isabelleErrors.contains("Undefined")) {
       processUndefined(filePath, safeLineNum, extractUndefined(isabelleErrors))
       return true
    }

    if (isabelleErrors.contains("exception THM 0 raised")) {
       injectLine(filePath, safeLineNum, removeTHM0(lineContent))
       return true
    }

    if (isabelleErrors.contains("Inner lexical error")) {
       if (containsUnicode(isabelleErrors)) {
          injectAll(filePath, replaceUnicode(extractText(filePath)))
          return true
       }
       invokeLLM()
       return true
    }

    println("Alternative error detected. Sending to LLM...")
    invokeLLM()
    true
  }
}