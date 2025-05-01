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
    val timeout = 30
    val sys_timeout = timeout.seconds
    val build_command = "~/Isabellm/Isabelle2022/bin/isabelle build -d /home/eaj123/Isabellm/Test Test"
    var iter = 0
    var done = false
    var filePath: String = ""
    var name: String = ""
    var command: String = ""
    val jsonPaths = mutable.Map[String, String]()

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

          // initialise json file for LLM history
          //name = extractName(statement)
          //val json_path = s"history/$name.json"
          //val jsonFile = new File(json_path)
          //if (!jsonFile.exists()) {
          //  history.jsonCreate(name)
          //}
          
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

          // FAILED PROOF ***********************************************************************************
          else if (isabelleErrors.contains("Failed to apply initial proof method")) {

            // NO SUBGOALS! ***********************************************************
            if (isabelleErrors.contains("No subgoals!")) {
              println("No subgoals detected! tidying proof...")
              injectLine(filePath, lineNum, "")
            } else {

              //injectLine(filePath, lineNum, "")
              val command = extractCommand(isabelleErrors)
              println(s"Command: $command")
              val all_text = extractToKeyword(filePath, lineNum, command)
              println("Failed to finish proof. Running Sledgehammer...")
              val (success, (message, solution)) = sledgehammer.call_sledgehammer(all_text, filePath)

              if (success) {
                
                println("Sledgehammer found a solution!")
                val proof = extractProof(solution.head)
                println(proof)
                //println(solution)
                extractKeyword(filePath,lineNum, command)
                injectProof(filePath, lineNum, proof)
                //injectLine(filePath, lineNum, proof)

              }

              else {
                println("Sledgehammer failed to find a solution.")
                extractKeyword(filePath, lineNum, command)
                injectSorry(filePath, lineNum)
              }
              }
          }

          // FAILED TO FINISH PROOF **************************************************************
          else if (isabelleErrors.contains("Failed to finish proof")) {

            //injectLine(filePath, lineNum, "")
            val command = extractCommand(isabelleErrors)
            println(s"Command: $command")
            val all_text = extractToKeyword(filePath, lineNum, command)
            println("Failed to finish proof. Running Sledgehammer...")
            val (success, (message, solution)) = sledgehammer.call_sledgehammer(all_text, filePath)

            if (success) {
              
              println("Sledgehammer found a solution!")
              val proof = extractProof(solution.head)
              println(proof)
              //println(solution)
              extractKeyword(filePath,lineNum, command)
              injectProof(filePath, lineNum, proof)
              //injectLine(filePath, lineNum, proof)

            }

            else {
              println("Sledgehammer failed to find a solution.")
              extractKeyword(filePath, lineNum, command)
              injectSorry(filePath, lineNum)
            }
          }

          // MALFORMED THEORY**************************************************************
          else if (isabelleErrors.contains("Malformed theory")) {
            
            println("Malformed")
            val all_text = extractAll(filePath,lineNum)
            println("Failed to finish proof. Running Sledgehammer...")
            val (success, (message, solution)) = sledgehammer.call_sledgehammer(all_text, filePath)

            if (success) {
              
              println("Sledgehammer found a solution!")
              val proof = extractProof(solution.head)

              println(proof)
              //injectLine(filePath, lineNum, solution)

            }

            else {
              println("Sledgehammer failed to find a solution.")
            }
          }


          
          // INNER LEXICAL ERROR *****************************************************************
          else if (isabelleErrors.contains("Inner lexical error")) {
            
            // UNICODE ERROR *******************************************************************
            if (containsUnicode(isabelleErrors)) {

              println("Modifying UniCode Symbols...")
              val all_text = extract.extractText(filePath)
              val replaced_text = replaceUnicode(all_text)
              inject.injectAll(filePath, replaced_text)

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

          //filePath = "/home/eaj123/Isabellm/Test/test.thy"
          //name = "obtainmax"
          //command = "by"

          val (start, end) = findLines(filePath, name)
          println(start, end)
          val tactic_line = tacticSearch(filePath, start, end)
          val all_text = extractToKeyword(filePath, tactic_line, command)
          println("Hammering timed-out tactics...")
          val (success, (message, solution)) = sledgehammer.call_sledgehammer(all_text, filePath)


          //val clean_lemma = removeTactics(lemma_all)
          //println(clean_lemma)
          //injectLemma(clean_lemma, filePath, start)
          
          //val all_text = extractText(filePath)
          

          if (success) {
              
              println("Sledgehammer found a solution!")
              val proof = extractProof(solution.head)
              println(proof)

              if (proof.contains("metis") || proof.contains("blast")) {
                println("labelling tactic as safe...")
                val safe_proof = proof + "(*SAFE*)"
                injectLine(filePath, tactic_line+1, safe_proof)
              } else {

                injectLine(filePath, tactic_line+1, proof)
              }
                            

            }

            else {
              println("Sledgehammer failed to find a solution.")
              
            }
      }
    }
    println(s"Exiting after $iter LLM iteration(s).")
  }
}
