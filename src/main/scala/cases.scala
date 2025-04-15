import java.io.PrintWriter



object errorCases {

    def extractUndefined(errorMsg: String): Option[String] = {
        val pattern = """Undefined (?:method|fact):\s*"([^"]+)"""".r
        pattern.findFirstMatchIn(errorMsg).map(_.group(1))
    }
    
    def removeWord(filePath: String, lineNumber: Int, word: String): Unit = {

        val expandedPath = filePath.replaceFirst("^~", System.getProperty("user.home"))
        val source = scala.io.Source.fromFile(expandedPath)
        val lines = source.getLines().toList
        source.close()

        val updatedLines = lines.zipWithIndex.map {
            case (line, idx) if idx == (lineNumber - 1) =>
            // Remove the word, optional trailing semicolon, and trim spacing
            line.replaceAll("""\b""" + java.util.regex.Pattern.quote(word) + """\b\s*;?""", "").trim
            case (line, _) => line
        }

        val writer = new PrintWriter(expandedPath)
        updatedLines.foreach(writer.println)
        writer.close()
    }
}