// UTILITIES FOR HANDLING THE OUTPUT OF THE LLM API

object llmOutput {

    val unicodeMap = Map(
            '∈' -> "\\<in>",
            '∉' -> "\\<notin>",
            '∧' -> "\\<and>",
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
            '⟹' -> "\\<Longrightarrow>"
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
    def extractCode(input: String): String = {

        val pattern = """(?s)```[a-zA-Z0-9]*\s*(.*?)```""".r

        pattern.findFirstMatchIn(input) match {
            case Some(m) =>
                println("Extracting Isabelle Code...")
                m.group(1).trim
            case None => input
        }
    }

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
}