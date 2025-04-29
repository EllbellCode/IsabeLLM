import scala.sys.process._
import scala.util.{Try, Success, Failure}
import java.io.{ByteArrayOutputStream, PrintStream}
import java.io.PrintWriter
import java.io.File

import ujson._
import extract._
import inject._
import history._
import sledgehammer._
import llmOutput._
import undefined._

object isabellm {
  def main(args: Array[String]): Unit = {
    
    val command = "~/Isabellm/Isabelle2022/bin/isabelle build -d /home/eaj123/Isabellm/Test Test"
    val maxIters = 8
    var iter = 0
    var done = false

    while (iter < maxIters && !done) {

      // Buffer to capture standard output (stdout)
      val stdoutBuffer = new StringBuilder
      

      val logger = ProcessLogger(
        (out: String) => stdoutBuffer.append(out + "\n")
      )

      // Run the command and capture output
      val exitCodeTry = Try {
        Seq("bash", "-c", command).!(logger)
      }
      
      exitCodeTry match {

        case Success(0) =>
          println("✅ .thy file built successfully.")
          done = true
          
        case Success(1) =>
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

          val (lineNum, filePath) = extract.extractLineAndPath(isabelleErrors).getOrElse((0, "default/path"))
          val thy = extract.extractThy(filePath, lineNum)
          val statement = extract.extractStatement(filePath, lineNum)
          val line = extract.extractLine(filePath, lineNum)

          // initialise json file for LLM history
          val name = extract.extractName(statement)
          val json_path = s"history/$name.json"
          val jsonFile = new File(json_path)
          if (!jsonFile.exists()) {
            history.jsonCreate(name)
          }
          
          // SORRY DETECTED IN PROOF ************************************************************************
          if (isabelleErrors.contains("quick_and_dirty")) {
            
            println("Sorry detected in lemma, sending to llm for proof.")
            println(s"LLM Iteration ${iter + 1} of $maxIters")

            //Call the Python script and pass the file path
            val pythonCommand: Seq[String] = 
              Seq("python3", "src/main/python/send_to_llm.py", thy, statement, isabelleErrors, line, json_path)
            val llm_output = pythonCommand.!!

            val parsed = ujson.read(llm_output)
            val input = parsed("input").str
            val output = parsed("output").str


            if (output.nonEmpty) {
              
              println("LLM OUTPUT************************************")
              println(output)

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

              println("Proof Failed. Making changes...")
            

              val all_text = extract.extractText(filePath)
              val (success, (message, solution)) = sledgehammer.call_sledgehammer(all_text, filePath)

              if (success) {
                
                println("Sledgehammer found a solution!")

              } else {
                
                println("Sledgehammer failed to find a solution.")
                println("Sending to llm for proof...")
                println(s"LLM Iteration ${iter + 1} of $maxIters")

                val pythonCommand: Seq[String] = 
                  Seq("python3", "src/main/python/send_to_llm.py", thy, statement, isabelleErrors, line, json_path)
                val llm_output = pythonCommand.!!
                iter += 1

                val parsed = ujson.read(llm_output)
                val input = parsed("input").str
                val output = parsed("output").str

                if (output.nonEmpty) {
                
                  println("LLM OUTPUT************************************")
                  println(output)

                  val refined_output = processOutput(output)

                  inject.injectLemma(refined_output, filePath, lineNum)

                  iter += 1

                } else {
                  println(s"Warning: No output received from LLM. Skipping iteration.")
                }
              }
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
          
        case Success(otherCode) =>
          println(s"❌ Command completed but returned unexpected exit code: $otherCode")
          println(s"Standard output:\n$stdoutBuffer")
          done = true
          
        case Failure(exception) =>
          println(s"🚨 Command execution failed with exception: ${exception.getMessage}")
          println(s"Captured stdout before failure:\n$stdoutBuffer")
          done = true
          
      }
    }
    println(s"Exiting after $iter LLM iteration(s).")
  }
}
