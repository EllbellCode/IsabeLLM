// UTILITIES FOR HANDLING THE OUTPUT OF THE LLM API

import java.io.File
import scala.sys.process._

import extract._


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
    def extractCode(input: String): String = {

        val backtickPattern = """(?s)```(?:isabelle)?\s*(.*?)```""".r
        val statementPattern = """(?s)\b(lemma|theorem|proposition|corollary)\b.*?(?=\n{2,}|$)""".r

        backtickPattern.findFirstMatchIn(input) match {
            case Some(m) =>
                println("Extracting Isabelle Code from backticks...")
                m.group(1).trim
            case None =>
                statementPattern.findFirstMatchIn(input) match {
                    case Some(m2) =>
                        println("Extracting Isabelle code from plain text...")
                        m2.matched.trim
                    case None =>
                        ""
                }
        }
    }

    // Replaces occurences of "apply" with by to maintain Isar
    def replaceApply(input: String): String = {
        input.replaceAll("\\bapply\\b", "by")
    }

    // Applies all of the refining utilities
    def processOutput(input: String): String = {
        
        println("Processing output...")
        val unicode_step = replaceUnicode(input)
        val code_step = extractCode(unicode_step)
        val apply_step = replaceApply(code_step)
        apply_step

    }

    // Calls the llm and handles the output
    def callLLM(thy: String, statement: String, error: String, line: String, jsonPath: String): Unit = {

        val (lineNum, extractedPath) = extractLineAndPath(error).getOrElse((0, "default/path"))
        val filePath = extractedPath

        var success = false

        while (!success) {
            
            println("Querying the LLM...")
    
            try {
                val pythonCommand: Seq[String] =
                    Seq("python3", "src/main/python/send_to_llm.py", thy, statement, error, line, jsonPath)
    
                val llm_output = pythonCommand.!!
                val parsed = ujson.read(llm_output)
                val input = parsed("input").str
                val output = parsed("output").str
    
                if (output.nonEmpty) {
                    println("LLM OUTPUT************************************")
                    println(output)
                    println("**********************************************")
    
                    val refined_output = processOutput(output)
    
                    if (refined_output.nonEmpty) {
                        inject.injectLemma(refined_output, filePath, lineNum)
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