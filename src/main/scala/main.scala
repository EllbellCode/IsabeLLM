import scala.sys.process._
import scala.util.{Try, Success, Failure}
import scala.concurrent.{Future, Await, blocking}
import scala.concurrent.duration._
import scala.collection.mutable
import java.util.concurrent.TimeoutException
import java.util.concurrent.{Executors, TimeUnit}
import java.io.{ByteArrayOutputStream, PrintStream}
import java.io.PrintWriter
import java.io.File
import ujson._
import scala.concurrent.ExecutionContext.Implicits.global

import extract._
import inject._
import history._
import sledgehammer._
import llmOutput._
import undefined._
import timeout._

object isabellm {

  def main(args: Array[String]): Unit = {
    
    val maxIters = 10
    val timeout = 30
    val sys_timeout = timeout.seconds
    val build_command = "~/Isabellm/Isabelle2022/bin/isabelle build -d /home/eaj123/Isabellm/Test Test"
    var iter = 0
    var done = false
    var filePath: String = ""
    var name: String = ""
    var command: String = ""
    var preservedError: Option[String] = None
    var preservedLine: Option[String] = None
    val jsonPaths = mutable.Map[String, String]()

    Seq("bash", "-c", "deactivate")

    while (iter < maxIters && !done) {

      if (!filePath.isEmpty) {

        val all_text = extract.extractText(filePath)
        val replaced_text = replaceUnicode(all_text)
        injectAll(filePath, replaced_text)

      }

      // Buffer to capture standard output (stdout)
      val stdoutBuffer = new StringBuilder
      

      val logger = ProcessLogger(
        (out: String) => stdoutBuffer.append(out + "\n")
      )

      println("Building theory...")
      // Run the command and capture output
      val exitCodeTry = Future {
        Seq("bash", "-c", build_command).!(logger)
      }
      
      try {

        val exitCode = Await.result(exitCodeTry, sys_timeout)
        //println(exitCode)

        if (exitCode == 0) {
          println("✅ .thy file built successfully.")
          done = true
        } else if (exitCode == 142) {

          println("Isabelle Timeout...")
          
        } else if (exitCode == 1) {

          println("⚠️ Encountered error during build.")
          //println(s"Standard output:\n$stdoutBuffer")

          // Extract Isabelle-style error lines
          val isabelleErrors = stdoutBuffer.linesIterator
            .filter(_.trim.startsWith("***"))
            .map(_.trim.stripPrefix("***").trim)
            .mkString("\n")


          println("❗ Extracted Isabelle errors:")
          println("********************************")
          println(isabelleErrors)
          println("********************************")

          var (lineNum, extractedPath) = extractLineAndPath(isabelleErrors).getOrElse((0, "default/path"))
          filePath = extractedPath
          val thy = extractThy(filePath, lineNum)
          val statement = extractAll(filePath, lineNum)
          val line = extractLine(filePath, lineNum)

          name = extractName(statement)

          val json_path = jsonPaths.getOrElseUpdate(name, {
            val freshPath = getUniqueJsonPath("history", name)
            jsonCreate(new File(freshPath).getName.stripSuffix(".json"))
            freshPath
          })
          
          // SORRY DETECTED IN PROOF ************************************************************************
          if (isabelleErrors.contains("quick_and_dirty")) {
            
            println("Sorry detected in lemma, sending to LLM for proof...")
            println(s"LLM Iteration ${iter + 1} of $maxIters")

            (preservedError, preservedLine) match {
              case (Some(prevErr), Some(prevLine)) =>
                callLLM(thy, statement, prevErr, prevLine, json_path)
                preservedError = None
                preservedLine = None
              case _ =>
                callLLM(thy, statement, isabelleErrors, line, json_path)
            }

            iter += 1
            
          }

          // FAILED PROOF ***********************************************************************************
          else if (isabelleErrors.contains("Failed to apply initial proof method")) {

            // NO SUBGOALS! ***********************************************************
            if (isabelleErrors.contains("No subgoals!")) {
              println("No subgoals detected! tidying proof...")
              injectLine(filePath, lineNum, "")
            } else {

              val fixLocale = localeFix(filePath, name)

              if (fixLocale) {
                lineNum += 1
              }

              val hammerProof = sledgehammerAll(filePath, lineNum, isabelleErrors)
              
              if (!hammerProof) {
                println("Preserving Errors...")
                preservedError = Some(isabelleErrors)
                preservedLine = Some(line)
              }

            }
          }

          // FAILED TO FINISH PROOF **************************************************************
          else if (isabelleErrors.contains("Failed to finish proof")) {
            
            val wasModified = assmsFix(filePath, name)

            if (!wasModified) {


              val hammerProof = sledgehammerAll(filePath, lineNum, isabelleErrors)
              
              if (!hammerProof) {
                println("Preserving Errors...")
                preservedError = Some(isabelleErrors)
                preservedLine = Some(line)
                //println(preservedError)
                //println(preservedLine)
              }

            } else {
              println("assmsFix modified the file. Rebuilding...")
            }
          }

          //MALFORMED COMMAND SYNTAX **********************************************************
          else if (isabelleErrors.contains("Malformed command syntax")) {

            val hammerProof = sledgehammerAll(filePath, lineNum, isabelleErrors)
              
            if (!hammerProof) {
              println("Preserving Errors...")
              preservedError = Some(isabelleErrors)
              preservedLine = Some(line)
            }
          }
 
          // INNER LEXICAL ERROR *****************************************************************
          else if (isabelleErrors.contains("Inner lexical error")) {
            
            // UNICODE ERROR *******************************************************************
            if (containsUnicode(isabelleErrors)) {

              val all_text = extract.extractText(filePath)
              val replaced_text = replaceUnicode(all_text)
              injectAll(filePath, replaced_text)

            }

            else {

               println("Unbound schematic variable, sending to LLM for correction...")
              println(s"LLM Iteration ${iter + 1} of $maxIters")

              callLLM(thy, statement, isabelleErrors, line, json_path)
              iter += 1
            }
            

          }

          // SYNTAX ERROR ******************************************************************************
          else if (isabelleErrors.contains("Outer syntax error")) {

            println("Isabelle encountered an Outer Syntax Error.")
            println("Please check the .thy file for syntax issues.")
            done= true
          }

          // BAD CONTEXT ******************************************************************************
          else if (isabelleErrors.contains("exception THM 0 raised")) {
            println("THM0. Removing OF...")
            val thm0_line = extractLine(filePath, lineNum)
            val thm0_fixed = removeTHM0(thm0_line)
            injectLine(filePath, lineNum, thm0_fixed)
          }

          // BAD CONTEXT ******************************************************************************
          else if (isabelleErrors.contains("Bad context")) {
            println("Bad Context. Removing Line...")
            injectLine(filePath, lineNum, "")
          }

          // UNDEFINED METHOD/FACT ***********************************************************
          else if (isabelleErrors.contains("Undefined")) {

            val undef_word = extractUndefined(isabelleErrors)
             println(s"Undefined Fact/Method: $undef_word")
            processUndefined(filePath, lineNum, undef_word)

          }

          else if (isabelleErrors.contains("Bad fact selection")) {

           // LOGIC FOR BAD FACT SELECTION *****************************************************

          // ALL OTHER ERRORS ***************************************************************
          } else {

            println("Alternative error detected. Sending to LLM for correction...")
            println(s"LLM Iteration ${iter + 1} of $maxIters")

            callLLM(thy, statement, isabelleErrors, line, json_path)
            iter += 1

          }   
        
        } 
      } catch {

        case e: TimeoutException =>
          println(s"🚨 Timeout exceeded after $sys_timeout.")

          //filePath = "/home/eaj123/Isabellm/Test/test.thy"
          //name = "n_consensus"
          //command = "by"

          //DOES NOT WORK IF IT IS THE FIRST CALL
          val wasModified = assmsFix(filePath, name)

          // If assmsFix modified the file, skip the rest of the block
          if (!wasModified) {

            val (start, end) = findLines(filePath, name)
            println(start, end)
            val tactic_line = tacticSearch(filePath, start, end)+1
            // modify to see if it has the SAFE tag to prevent checking
            // already verified lines
            println(s"Potential timeout issue found at line $tactic_line")
            val all_text = extractToKeyword(filePath, tactic_line, command)
            //println(all_text)
            println("Hammering timed-out tactics...")
            val (success, (message, solution)) = call_sledgehammer(all_text, filePath)

            if (success) {
                
                println("Sledgehammer found a solution!")
                val proof = extractProof(solution.head)
                println(proof)

                if (tacticKeywords.exists(proof.contains)) {
                  println("labelling tactic as safe...")
                  val safe_proof = proof + "(*SAFE*)"
                  extractKeyword(filePath, tactic_line, command)
                  injectProof(filePath, tactic_line, safe_proof)
                } else {

                  extractKeyword(filePath, tactic_line, command)
                  injectProof(filePath, tactic_line, proof)
                }

              }

              else {
                println("Sledgehammer failed to find a solution.")
                extractKeyword(filePath, tactic_line, command)
                injectProof(filePath, tactic_line, "sorry")
                println("Preserving Errors...")
                preservedError = Some("Failed to Finish Proof.")
                preservedLine = Some(extractLine(filePath, tactic_line))
                
              }
            
          } else {
            println("assmsFix modified the file.")
          }
      }
    }
    println(s"Exiting after $iter LLM iteration(s).")
  }
}
