
package llm

// UTILITIES FOR HANDLING THE OUTPUT OF THE LLM API

import java.io.File
import scala.sys.process._
import utils.extract._
import utils.inject._

object llmOutput {

    val unicodeMap = Map(
            '∈' -> "\\<in>",
            '∉' -> "\\<notin>",
            '∧' -> "\\<and>",
            '⋀' -> "\\<And>",
            '∨' -> "\\<or>",
            '¬' -> "\\<not>",
            '⇒' -> "\\<rightarrow>",
            '⇔' -> "\\<Longleftrightarrow>",
            '∀' -> "\\<forall>",
            '∃' -> "\\<exists>",
            '≠' -> "\\<noteq>",
            '≤' -> "\\<le>",
            '≥' -> "\\<ge>",
            '→' -> "\\<rightarrow>",
            '←' -> "\\<leftarrow>",
            '×' -> "\\<times>",
            '∅' -> "\\<emptyset>",
            '⟹' -> "\\<Longrightarrow>",
            '‹' -> "\\<open>",
            '›' -> "\\<close>",
            '⟦' -> "\\<lbrakk>",
            '⟧' -> "\\<rbrakk>",
            'λ' -> "\\<lambda>"
    )

    val tacticKeywords = Set("simp", "blast", "auto", "metis", "fastforce", "force", "presburger", "smt")

    def containsUnicode(input: String): Boolean = {
        unicodeMap.keys.exists(input.contains(_))
    }
    
    def replaceUnicode(input: String): String = {
        if (containsUnicode(input)) {
            println("Modifying UniCode Symbols...")
            input.flatMap { ch =>
                unicodeMap.getOrElse(ch, ch.toString)
            }.mkString
        } else {
            input
        }
    }

    def normalizeWhitespace(s: String): String = s.replaceAll("\\s+", " ").trim

    def findStartIndex(rawInput: String, normalizedStatement: String): Option[Int] = {
        val normalizedInput = normalizeWhitespace(rawInput)
        val startNormIndex = normalizedInput.indexOf(normalizedStatement)
        
        if (startNormIndex < 0) None
        else {
            var rawPos = 0
            var normPos = 0
            while (rawPos < rawInput.length && normPos < startNormIndex) {
                val c = rawInput.charAt(rawPos)
                if (Character.isWhitespace(c)) {
                    while (rawPos < rawInput.length && Character.isWhitespace(rawInput.charAt(rawPos))) rawPos += 1
                    normPos += 1 
                } else {
                    rawPos += 1
                    normPos += 1
                }
            }
            Some(rawPos)
        }
    }

    def findProofBlock(text: String): String = {
        val lines = text.linesIterator.toVector
        val lastQedIndex = lines.lastIndexWhere(_.trim.matches("""\bqed\b"""))
        val lastTacticIndex = lines.lastIndexWhere { line =>
            val l = line.trim.toLowerCase
            l.startsWith("by ") && tacticKeywords.exists(tk => l.contains(tk))
        }

        val endIndex = (lastQedIndex, lastTacticIndex) match {
            case (-1, -1) => lines.length - 1
            case (q, t) if q > t => q
            case (_, t) => t
        }

        lines.take(endIndex + 1).mkString("\n")
    }

    def extractCode(input: String, statement: String): String = {
        val backtickPattern = """(?s)```[^\n]*\n(.*?)```""".r
        
        backtickPattern.findFirstMatchIn(input) match {
            case Some(m) => 
                println("Extracting Isabelle code from backticks...")
                m.group(1).trim
            case None =>
                val normalizedStmt = normalizeWhitespace(statement)
                findStartIndex(input, normalizedStmt) match {
                    case Some(start) =>
                        println(s"Statement found at raw input index $start")
                        val after = input.substring(start)
                        findProofBlock(after).trim
                    case None =>
                        val lines = input.linesIterator.toVector
                        val startKeywords = Set("proof", "apply", "by", "lemma", "theorem", "proposition")
                        
                        val startLineIndex = lines.indexWhere { line => 
                            val t = line.trim
                            startKeywords.exists(kw => t.startsWith(kw) && (t.length == kw.length || !t(kw.length).isLetterOrDigit))
                        }

                        if (startLineIndex != -1) {
                             println(s"Found raw code start at line ${startLineIndex + 1}")
                             val codeBlock = lines.drop(startLineIndex).mkString("\n")
                             findProofBlock(codeBlock).trim
                        } else {
                             println("No code block found.")
                             ""
                        }
                }
        }
    }

    def replaceApply(input: String): String = {
        input.replaceAll("\\bapply\\b", "by")
    }

    def processOutput(input: String, statement: String): String = {
        println("Processing output...")
        val unicodeStep = replaceUnicode(input)
        val rawCode = extractCode(unicodeStep, statement)
        
        if (rawCode.nonEmpty) {
            val applyStep = replaceApply(rawCode)
            applyStep
        } else {
            ""
        }
    }

    def callLLM(
        currentThyContent: String, 
        all: String, 
        statement: String, 
        error: String, 
        line: String, 
        jsonPath: String, 
        filePath: String,
        lineNum: Int,
        errorTrace: String // New Argument
    ): Option[String] = {
        
        var result: Option[String] = None
        var success = false
        var attempts = 0
        val maxAttempts = 1
        
        while (!success && attempts < maxAttempts) {
            attempts += 1
            try {
                val stderr = new StringBuilder
                val stdout = new StringBuilder

                val scriptPath = "src/main/python/send_to_llm.py" 
                // Passed errorTrace as the last argument
                val pythonCommand = Seq("python3", scriptPath, currentThyContent, all, error, line, jsonPath, errorTrace)

                println("Querying the LLM...")
                val exitCode = pythonCommand ! ProcessLogger(stdout.append(_), stderr.append(_))

                val llm_output = stdout.toString().trim

                // println(s"RAW OUTPUT: [$llm_output]")

                // if (stderr.nonEmpty) {
                //     println(s"🐍 Python Logs:\n$stderr")
                // }

                if (exitCode != 0 || llm_output.isEmpty) {
                    println(s"❌ Python script failed with exit code $exitCode")
                }

                val parsed = ujson.read(llm_output)
                val output = parsed("output").str

                println(s"PARSED OUTPUT: [$output]")

                if (output.nonEmpty) {
                    val refined_output = processOutput(output, statement)
                    println(s"OUTPUT: [$refined_output']")
                    
                    if (refined_output.nonEmpty) {
                        println(s"Injecting following proof into $filePath at line $lineNum:")
                        result = Some(refined_output)
                        success = true
                    } else {
                        println("Warning: Extracted code was empty.")
                    }
                } else {
                    println("❌ LLM returned empty output. Python stderr:")
                    println(stderr.toString()) 
                }
            } catch {
                case e: Exception => 
                    println(s"LLM call failed: ${e.getMessage}")
                    if (attempts >= maxAttempts) return None 
            }
        }
        result
    }
}