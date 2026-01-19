package utils

import java.io.{PrintWriter, File}
import scala.io.Source

object undefined {
    
    val methods = Set("Cons")
    val suffix = Set("IH")

    // Helper to read file content safely
    def readFile(path: String): String = {
        val source = Source.fromFile(path)
        try source.getLines().mkString("\n") finally source.close()
    }

    // Helper to write content back to disk
    def writeFile(path: String, content: String): Unit = {
        val writer = new PrintWriter(new File(path))
        try writer.write(content) finally writer.close()
    }

    def extractUndefined(errorMsg: String): String = 
        """Undefined (?:method|fact):\s*"([^"]+)"""".r.findFirstMatchIn(errorMsg).map(_.group(1)).getOrElse("")

    def removeWord(currentText: String, lineNumber: Int, word: String): String = {
        val lines = currentText.split("\n", -1).toList
        val pattern = ("""(\s*|;)""" + java.util.regex.Pattern.quote(word) + """(\[[^\]]*\])?""").r

        lines.zipWithIndex.map {
            case (line, idx) if idx == lineNumber - 1 => pattern.replaceAllIn(line, "").replaceAll("\\s+", " ").trim
            case (line, _) => line
        }.mkString("\n")
    }
    
    def replaceWord(currentText: String, lineNumber: Int, oldWord: String, newWord: String): String = {
        val lines = currentText.split("\n", -1).toList
        lines.zipWithIndex.map {
            case (line, idx) if idx == lineNumber - 1 => line.replaceAll(java.util.regex.Pattern.quote(oldWord), newWord)
            case (line, _) => line
        }.mkString("\n")
    }

    def removeTHM0(input: String): String = {
        val pattern = """\b\w+\[[^\[\]]*\]""".r
        pattern.replaceAllIn(input, m => {
            val word = m.matched.takeWhile(_ != '[')
            word
        })
    }

    def removeUsing(filePath: String, lineNumber: Int): Unit = {
        val expandedPath = filePath.replaceFirst("^~", System.getProperty("user.home"))
        
        // FIXED: Uses readFile/writeFile pattern (though manually implemented here to match original style)
        val source = scala.io.Source.fromFile(expandedPath)
        val lines = try source.getLines().toList finally source.close()

        val idx = lineNumber - 1
        val updatedLines = lines.zipWithIndex.map {
            case (line, i) if i == idx && line.contains("using by") =>
                // Remove "using" when followed by "by", keeping spacing clean
                line.replaceFirst("""\busing\b\s*""", "").replaceAll("\\s+", " ").trim
            case (line, _) => line
        }

        val writer = new PrintWriter(expandedPath)
        try updatedLines.foreach(writer.println) finally writer.close()
    }

    def checkUndefined(input: String): String = {
        methods.collectFirst {
            case method if input.startsWith(method) => method.stripSuffix(".")
        }.getOrElse(input)
    }

    def removeSuffix(input: String): String = {
        val pattern = raw"""(.*?)\.(${suffix.mkString("|")})\b""".r
        input match {
            case pattern(prefix, _) => prefix
            case _ => input
        }
    }

    // FIXED: Now takes filePath, reads content, modifies it, and WRITES IT BACK.
    def processUndefined(filePath: String, lineNumber: Int, word: String): Unit = {
        
        val currentText = readFile(filePath) // 1. Read
        
        val newText = if (methods.exists(word.contains)) {
            val newWord = methods.collectFirst { case m if word.startsWith(m) => m }.getOrElse(word)
            replaceWord(currentText, lineNumber, word, newWord)
        } else if (suffix.exists(s => word.endsWith("." + s))) {
            val newWord = word.split('.').head
            replaceWord(currentText, lineNumber, word, newWord)
        } else {
            val textWithoutWord = removeWord(currentText, lineNumber, word)
            
            // Logic to clean up "using by" artifacts if a word removal caused them
            val lines = textWithoutWord.split("\n", -1).toList
            lines.zipWithIndex.map {
                case (line, i) if i == lineNumber - 1 && line.contains("using by") =>
                    line.replaceFirst("""\busing\b\s*""", "").replaceAll("\\s+", " ").trim
                case (line, _) => line
            }.mkString("\n")
        }

        writeFile(filePath, newText) // 2. Write
    }
}