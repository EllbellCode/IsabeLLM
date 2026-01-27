
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

            // Add more mappings as needed
    )

    // Returns True if the inputted string contains a unicode symbol
    def containsUnicode(input: String): Boolean = {
        unicodeMap.keys.exists(input.contains(_))
    }
    
    // Replaces unicode symbols in the input with their 'plaintext' version
    def replaceUnicode(input: String): String = {
        
        if (containsUnicode(input)) {
            println("Modifying UniCode Symbols...")
            input.flatMap { ch =>
                unicodeMap.getOrElse(ch, ch.toString)
            }
        } else {
            input
        }
    }

    // Extract the Code between triple backticks if the string contains them
    // If string is raw code
    // Returns empty string if there is no code
    def extractCode(input: String, statement: String): String = {
        val backtickPattern = """(?s)```[^\n]*\n(.*?)```""".r

        val tacticKeywords = Set(
            "auto", "simp", "blast", "fastforce", "metis", "force", "presburger", "smt"
        )

        // Normalize whitespace (convert any whitespace runs to a single space)
        def normalizeWhitespace(s: String): String = s.replaceAll("\\s+", " ").trim

        // Try to find the start index of the normalized statement inside normalized input,
        // then map that back to raw input start index.
        def findStartIndex(rawInput: String, normalizedStatement: String): Option[Int] = {
            val normalizedInput = normalizeWhitespace(rawInput)
            val startNormIndex = normalizedInput.indexOf(normalizedStatement)
            if (startNormIndex < 0) None
            else {
            // We want to find where normalizedInput(startNormIndex) maps to in rawInput.
            // We'll scan rawInput while building normalizedInput and stop when lengths match.
            var rawPos = 0
            var normPos = 0
            while (rawPos < rawInput.length && normPos < startNormIndex) {
                val c = rawInput.charAt(rawPos)
                if (Character.isWhitespace(c)) {
                // Skip runs of whitespace in rawInput corresponding to single space in normalizedInput
                // But normalizedInput replaces all runs with single space so skip all whitespace here
                while (rawPos < rawInput.length && Character.isWhitespace(rawInput.charAt(rawPos))) rawPos += 1
                normPos += 1 // counted as single space
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
            // find last qed line
            val lastQedIndex = lines.lastIndexWhere(_.trim.matches("""\bqed\b"""))
            // find last tactic line
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
                println("No matching code block found.")
                ""
            }
        }
    }


    // Replaces occurences of "apply" with by to maintain Isar
    def replaceApply(input: String): String = {
        input.replaceAll("\\bapply\\b", "by")
    }

    // Applies all of the refining utilities
    def processOutput(input: String, statement: String): String = {
        
        println("Processing output...")
        val unicode_step = replaceUnicode(input)
        val code_step = extractCode(unicode_step, statement)
        val apply_step = replaceApply(code_step)
        apply_step

    }

    // Calls the llm and handles the output
    def callLLM(thy: String, all: String, statement: String, error: String, line: String, jsonPath: String): Unit = {

        val (lineNum, extractedPath) = extractLineAndPath(error).getOrElse((0, "default/path"))
        val filePath = extractedPath

        var success = false

        while (!success) {
            
            println("Querying the LLM...")
    
            try {
                val pythonCommand: Seq[String] =
                    Seq("python3", "src/main/python/send_to_llm.py", thy, all, error, line, jsonPath)
    
                val llm_output = pythonCommand.!!
                val parsed = ujson.read(llm_output)
                val input = parsed("input").str
                val output = parsed("output").str
    
                if (output.nonEmpty) {
                    println("LLM OUTPUT************************************")
                    println(output)
                    println("**********************************************")

                    val refined_output = processOutput(output, statement)
    
                    if (refined_output.nonEmpty) {
                        injectLemma(refined_output, filePath, lineNum)
                        success = true // exit loop
                    } else {
                        println("The LLM did not generate code in its response. Retrying...")
                    }
    
                } else {
                    println("Warning: No output received from LLM. Retrying...")
                }
    
            } catch {
                case e: Exception =>
                    println(s"Error during LLM call: ${e.getMessage}. Retrying...")
            }
        }

    }

}