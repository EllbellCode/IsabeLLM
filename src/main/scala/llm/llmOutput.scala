
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

    val tacticKeywords = Set("simp", "blast", "auto", "metis", "fastforce", "force", "presburger")

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

    def sanitise(s: String): String = {
        // Specifically targets Unicode non-breaking spaces + standard whitespace
        s.replaceAll("[\u00A0\\s]+", " ").trim
    }

    def extractCode(input: String, statement: String): String = {
        val backtickPattern = """(?s)```[^\n]*\n(.*?)```""".r
        
        backtickPattern.findFirstMatchIn(input) match {
            case Some(m) => m.group(1).trim
            case None =>
                val cleanInput = sanitise(input)
                val cleanStmt = sanitise(statement)

                if (cleanInput.contains(cleanStmt)) {
                    // Use the first line of the lemma as a search anchor in the raw text
                    val searchAnchor = statement.split("\n").head.trim.take(20)
                    val startIndex = input.indexOf(searchAnchor)
                    
                    if (startIndex != -1) {
                        // Extract from the lemma start to the 'qed' or last tactic
                        findProofBlock(input.substring(startIndex)).trim
                    } else {
                        input.trim
                    }
                } else {
                    // Fallback if the LLM only gave the proof body
                    if (input.toLowerCase.contains("proof")) findProofBlock(input).trim
                    else ""
                }
        }
    }

    def processOutput(input: String, statement: String): String = {
        println("Processing output...")
        
        val rawCode = extractCode(input, statement)
        
        if (rawCode.nonEmpty) {
            // Step 2: Transform symbols ONLY on the extracted code
            val unicodeStep = replaceUnicode(rawCode)
            val applyStep = replaceApply(unicodeStep)
            applyStep
        } else {
            ""
        }
    }

    def replaceApply(input: String): String = {
        input.replaceAll("\\bapply\\b", "by")
    }

    def callLLM(
        currentThyContent: String, 
        all: String, 
        statement: String, 
        error: String, 
        line: String, 
        jsonPath: String, 
        filePath: String,
        lineNum: Int  // NEW: Pass the integer line number directly
    ): Option[String] = {
        
        // REMOVED: The old logic that tried to extract line from the 'error' string
        
        var result: Option[String] = None
        var success = false
        var attempts = 0
        val maxAttempts = 1
        
        while (!success && attempts < maxAttempts) {
            attempts += 1
            try {
                val stderr = new StringBuilder
                val stdout = new StringBuilder

                val scriptPath = "/home/eaj123/PhDLinux/Isabellm/Test/src/main/python/send_to_llm.py"
                val pythonCommand = Seq("python3", scriptPath, currentThyContent, all, error, line, jsonPath)

                val exitCode = pythonCommand ! ProcessLogger(stdout.append(_), stderr.append(_))
                val llm_output = stdout.toString().trim

                if (exitCode != 0 || llm_output.isEmpty) {
                    println(s"❌ Python script failed with exit code $exitCode")
                }

                val parsed = ujson.read(llm_output)
                val output = parsed("output").str

                if (output.nonEmpty) {
                    val refined_output = processOutput(output, statement)
                    println(refined_output)
                    if (refined_output.nonEmpty) {
                        
                        println(s"Injecting following proof into $filePath at line $lineNum:")
                        utils.inject.injectLemma(refined_output, filePath, lineNum) 
                        result = Some(refined_output)
                        success = true
                    }
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