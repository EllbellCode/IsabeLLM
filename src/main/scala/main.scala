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
    
    val maxIters = 8
    val timeout = 10
    val sys_timeout = timeout.seconds
    val build_command = "~/Isabellm/Isabelle2022/bin/isabelle build -d /home/eaj123/Isabellm/Test Test"
    var iter = 0
    var done = false
    var filePath: String = ""
    var name: String = ""
    var command: String = ""
    val jsonPaths = mutable.Map[String, String]()

    Seq("bash", "-c", "deactivate")

    while (iter < maxIters && !done) {

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

          println("⚠️ Command completed but returned exit code 1 (generic failure).")
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

          val (lineNum, extractedPath) = extractLineAndPath(isabelleErrors).getOrElse((0, "default/path"))
          filePath = extractedPath
          val thy = extractThy(filePath, lineNum)
          val statement = extractStatement(filePath, lineNum)
          val line = extractLine(filePath, lineNum)

          name = extractName(statement)

          val json_path = jsonPaths.getOrElseUpdate(name, {
            val freshPath = getUniqueJsonPath("history", name)
            jsonCreate(new File(freshPath).getName.stripSuffix(".json"))
            freshPath
          })
          
          // SORRY DETECTED IN PROOF ************************************************************************
          if (isabelleErrors.contains("quick_and_dirty")) {
            
            println("Sorry detected in lemma, sending to llm for proof.")
            println(s"LLM Iteration ${iter + 1} of $maxIters")

            //Call the Python script and pass the file path
            Seq("bash", "-c", "source /isabellm/bin/activate")
            val pythonCommand: Seq[String] = 
              Seq("python3", "src/main/python/send_to_llm.py", thy, statement, isabelleErrors, line, json_path)
            val llm_output = pythonCommand.!!
            Seq("bash", "-c", "deactivate")
            val parsed = ujson.read(llm_output)
            val input = parsed("input").str
            val output = parsed("output").str


            if (output.nonEmpty) {
              
              println("LLM OUTPUT************************************")
              println(output)
              println("**********************************************")

              val refined_output = processOutput(output)

              inject.injectLemma(refined_output, filePath, lineNum)

              iter += 1

            } else {
              println(s"Warning: No output received from LLM. Skipping iteration.")
            }
          }

          else if (isabelleErrors.contains("Type unification failed")) {

            println("Sorry detected in lemma, sending to llm for proof.")
            println(s"LLM Iteration ${iter + 1} of $maxIters")

            //Call the Python script and pass the file path
            Seq("bash", "-c", "source /isabellm/bin/activate")
            val pythonCommand: Seq[String] = 
              Seq("python3", "src/main/python/send_to_llm.py", thy, statement, isabelleErrors, line, json_path)
            val llm_output = pythonCommand.!!
            Seq("bash", "-c", "deactivate")
            val parsed = ujson.read(llm_output)
            val input = parsed("input").str
            val output = parsed("output").str


            if (output.nonEmpty) {
              
              println("LLM OUTPUT************************************")
              println(output)
              println("**********************************************")

              val refined_output = processOutput(output)

              inject.injectLemma(refined_output, filePath, lineNum)

              iter += 1

            } else {
              println(s"Warning: No output received from LLM. Skipping iteration.")
            }
          }

          // FAILED PROOF ***********************************************************************************
          else if (isabelleErrors.contains("Failed to apply initial proof method")) {

            // NO SUBGOALS! ***********************************************************
            if (isabelleErrors.contains("No subgoals!")) {
              println("No subgoals detected! tidying proof...")
              injectLine(filePath, lineNum, "")
            } else {

              sledgehammerAll(filePath, lineNum, isabelleErrors)

              }
          }

          // FAILED TO FINISH PROOF **************************************************************
          else if (isabelleErrors.contains("Failed to finish proof")) {
            
            val wasModified = assmsFix(filePath, name)

            // If assmsFix modified the file, skip the rest of the block
            if (!wasModified) {

              sledgehammerAll(filePath, lineNum, isabelleErrors)

            } else {
              println("assmsFix modified the file")
            }
          }

          // MALFORMED THEORY**************************************************************
          else if (isabelleErrors.contains("Malformed theory")) {
            
            sledgehammerAll(filePath, lineNum, isabelleErrors)

          }

          //MALFORMED COMMAND SYNTAX **********************************************************
          else if (isabelleErrors.contains("Malformed command syntax")) {

            sledgehammerAll(filePath, lineNum, isabelleErrors)
          }
 
          // INNER LEXICAL ERROR *****************************************************************
          else if (isabelleErrors.contains("Inner lexical error")) {
            
            // UNICODE ERROR *******************************************************************
            if (containsUnicode(isabelleErrors)) {

              println("Modifying UniCode Symbols...")
              val all_text = extract.extractText(filePath)
              val replaced_text = replaceUnicode(all_text)
              injectAll(filePath, replaced_text)

            }

            else {

              //CALL LLM HERE!
            }
            

          }
          // SYNTAX ERROR ******************************************************************************
          else if (isabelleErrors.contains("Outer syntax error")) {

            println("Isabelle encountered an Outer Syntax Error.")
            println("Please check the .thy file for syntax issues.")
            done= true
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
        }   
      } catch {

        case e: TimeoutException =>
          println(s"🚨 Timeout exceeded after $sys_timeout.")

          filePath = "/home/eaj123/Isabellm/Test/test.thy"
          name = "obtainmax"
          command = "by"

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
            println(all_text)
            println("Hammering timed-out tactics...")
            val (success, (message, solution)) = call_sledgehammer(all_text, filePath)

            if (success) {
                
                println("Sledgehammer found a solution!")
                val proof = extractProof(solution.head)
                println(proof)

                // change this to consider all unsafe tactics set
                if (proof.contains("metis") || proof.contains("blast")) {
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
                // Custom error for this
                
              }
            
          } else {
            println("assmsFix modified the file.")
          }
      }
    }
    println(s"Exiting after $iter LLM iteration(s).")
  }
}
