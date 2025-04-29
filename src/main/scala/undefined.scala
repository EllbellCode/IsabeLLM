import java.io.PrintWriter



object undefined {
    
     val methods = Set(
        "Cons"
    )

    // Extracts the undefined word/tactic/theory from the error message**********************
    def extractUndefined(errorMsg: String): String = {
        val pattern = """Undefined (?:method|fact):\s*"([^"]+)"""".r
        pattern.findFirstMatchIn(errorMsg).map(_.group(1)).getOrElse("")
    }
    
    // Removes the given word from a line in the file **************************************
    def removeWord(filePath: String, lineNumber: Int, word: String): Unit = {

        val expandedPath = filePath.replaceFirst("^~", System.getProperty("user.home"))
        val source = scala.io.Source.fromFile(expandedPath)
        val lines = source.getLines().toList
        source.close()

        val pattern = ("""(\s*|;)""" + java.util.regex.Pattern.quote(word) + """(?:\(\d+\))?""").r

        val updatedLines = lines.zipWithIndex.map {
            case (line, idx) if idx == (lineNumber - 1) =>
                pattern.replaceAllIn(line, "").replaceAll("\\s+", " ").trim
            case (line, _) => line
        }

        val writer = new PrintWriter(expandedPath)
        updatedLines.foreach(writer.println)
        writer.close()
    }

    // Replaces oldWord with newWord in a given line in a given file ****************************
    def replaceWord(filePath: String, lineNumber: Int, oldWord: String, newWord: String): Unit = {

        val expandedPath = filePath.replaceFirst("^~", System.getProperty("user.home"))
        val source = scala.io.Source.fromFile(expandedPath)
        val lines = source.getLines().toList
        source.close()

        val updatedLines = lines.zipWithIndex.map {
            case (line, idx) if idx == (lineNumber - 1) =>
            val pattern = java.util.regex.Pattern.quote(oldWord)
            line.replaceAll(pattern, newWord)
            case (line, _) => line
        }

        val writer = new PrintWriter(expandedPath)
        updatedLines.foreach(writer.println)
        writer.close()
    }

    // Checks if the undefined word is a derivative of a commom Isabelle method
    // Returns the method if it is ***********************************************************
    def checkUndefined(input: String): String = {
        
        methods.collectFirst {
            case method if input.startsWith(method) => method.stripSuffix(".")
        }.getOrElse(input)
    }

    def processUndefined(filePath: String, lineNumber: Int, word: String): Unit = {

        if (methods.exists(word.contains)) {
            println("Modifying method...")
            val newWord = checkUndefined(word)
            replaceWord(filePath, lineNumber, word, newWord)
        } else {
            println("Removing method...")
            removeWord(filePath, lineNumber, word)
        }
    }
}