import scala.sys.process._
import scala.util.{Try, Success, Failure}
import java.io.{ByteArrayOutputStream, PrintStream}
import java.io.PrintWriter

import extract._
import inject._

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
          println(isabelleErrors)
          
          if (isabelleErrors.contains("quick_and_dirty")) {
            
            println("Sorry detected in lemma, sending to llm for proof.")
            println(s"LLM Iteration ${iter + 1} of $maxIters")

            val (lineNum, filePath) = extract.extractLineAndPath(isabelleErrors).getOrElse((0, "default/path"))
            val thy = extract.extractThy(filePath, lineNum)
            val lemma = extract.extractStatement(filePath, lineNum)
            val line = extract.extractLine(filePath, lineNum)
            val mode = 0  // First call to llm for this lemma

            //Call the Python script and pass the file path
            val pythonCommand: Seq[String] = Seq("python3", "src/main/python/send_to_llm.py", thy, lemma, isabelleErrors, line, mode.toString)
            val llm_output = pythonCommand.!!
            iter += 1

            val pattern = "===OUTPUT===\\s*".r
            val parts = pattern.split(llm_output)  // limit = 2 to avoid over-splitting

            val inputPart = parts.headOption.map(_.replace("===INPUT===", "").trim).getOrElse("")
            val outputPart = parts.lift(1).getOrElse("").trim

            //println("Input:")
            //println(inputPart)
            println("LLM OUTPUT************************************")
            println(outputPart)

            inject.injectLemma(outputPart, filePath, lineNum)

          }

          else if (isabelleErrors.contains("Failed to apply initial proof method")) {
            
            println("Proof Failed. Making changes...")

            val (lineNum, filePath) = extract.extractLineAndPath(isabelleErrors).getOrElse((0, "default/path"))
            val thy = extract.extractThy(filePath, lineNum)
            val lemma = extract.extractStatement(filePath, lineNum)
            val line = extract.extractLine(filePath, lineNum)
            val mode = 1  // First call to llm for this lemma
            
            // SLEDGEHAMMER HERE *****************************************************************************
            // If sledgehammer solves, finish here
            // Else, send to LLM
            //Call the Python script and pass the file path
            println("Sending to llm for proof...")
            println(s"LLM Iteration ${iter + 1} of $maxIters")

            val pythonCommand: Seq[String] = Seq("python3", "src/main/python/send_to_llm.py", thy, lemma, isabelleErrors, line, mode.toString)
            val llm_output = pythonCommand.!!
            iter += 1

            val pattern = "===OUTPUT===\\s*".r
            val parts = pattern.split(llm_output)  // limit = 2 to avoid over-splitting

            val inputPart = parts.headOption.map(_.replace("===INPUT===", "").trim).getOrElse("")
            val outputPart = parts.lift(1).getOrElse("").trim

            //println("Input:")
            //println(inputPart)
            println("LLM OUTPUT************************************")
            println(outputPart)

            inject.injectLemma(outputPart, filePath, lineNum)

          }

          else if (isabelleErrors.contains("Outer syntax error")) {

            println("Isabelle encountered an Outer Syntax Error.")
            println("Please check the .thy file for syntax issues.")
            done= true

          }

          // Can be Undefined Method or Fact
          else if (isabelleErrors.contains("Undefined")) {

            println("Undefined Fact/Method.")
            val undef_word = errorCases.extractUndefined(isabelleErrors).getOrElse((""))
            val (lineNum, filePath) = extract.extractLineAndPath(isabelleErrors).getOrElse((0, "default/path"))
            errorCases.removeWord(filePath, lineNum, undef_word)

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
