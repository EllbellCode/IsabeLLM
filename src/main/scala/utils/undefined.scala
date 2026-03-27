package utils

import java.io.{PrintWriter, File}
import scala.io.Source
import java.util.regex.Pattern

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
        
        val qWord = java.util.regex.Pattern.quote(word)
        
        val pattern = s"""(?<![\\w'])$qWord(?![\\w'])\\s*,?""".r

        lines.zipWithIndex.map {
            case (line, idx) if idx == lineNumber - 1 =>
                val indentation = line.takeWhile(_.isWhitespace)
                
                var cleaned = pattern.replaceAllIn(line, "")
                
                cleaned = cleaned.replace("(, ", "(").replace("(,", "(")
                cleaned = cleaned.replace(", )", ")").replace(",)", ")")
                cleaned = cleaned.replaceAll(",\\s*,", ",")
                
                cleaned = cleaned.replace("( )", "").replace("()", "")
                
                cleaned = cleaned.replaceAll("\\s+", " ").trim
                
                if (cleaned.isEmpty) "" else indentation + cleaned
                
            case (line, _) => line
        }.mkString("\n")
    }
    
    def replaceWord(currentText: String, lineNumber: Int, oldWord: String, newWord: String): String = {
        val lines = currentText.split("\n", -1).toList
        lines.zipWithIndex.map {
            case (line, idx) if idx == lineNumber - 1 => line.replaceAll(Pattern.quote(oldWord), newWord)
            case (line, _) => line
        }.mkString("\n")
    }

    def removeTHM0(input: String): String = {
        val pattern = """[\w'\(\)\.]+\s*\[[^\[\]]*\]""".r
        pattern.replaceAllIn(input, m => {
            val word = m.matched.takeWhile(_ != '[')
            word.trim
        })
    }

    def removeUsing(filePath: String, lineNumber: Int): Unit = {
        val expandedPath = filePath.replaceFirst("^~", System.getProperty("user.home"))
        val source = scala.io.Source.fromFile(expandedPath)
        val lines = try source.getLines().toList finally source.close()

        val idx = lineNumber - 1
        val updatedLines = lines.zipWithIndex.map {
            case (line, i) if i == idx && line.contains("using by") =>
                line.replaceFirst("""\busing\b\s*""", "").replaceAll("\\s+", " ").trim
            case (line, _) => line
        }

        val writer = new PrintWriter(expandedPath)
        try updatedLines.foreach(writer.println) finally writer.close()
    }
    
    def processLiteralRemoval(filePath: String, lineNumber: Int, fact: String): Boolean = {
        val currentText = readFile(filePath)
        val lines = currentText.split("\n", -1).toBuffer
        
        if (lineNumber < 1 || lineNumber > lines.length) return false
        
        val lineContent = lines(lineNumber - 1)
        
        val replacements = Map(
            "∈" -> "\\<in>", "∉" -> "\\<notin>", "∀" -> "\\<forall>", 
            "∃" -> "\\<exists>", "⟶" -> "\\<longrightarrow>", "⟹" -> "\\<Longrightarrow>",
            "∧" -> "\\<and>", "∨" -> "\\<or>", "≤" -> "\\<le>", "≥" -> "\\<ge>"
        )
        val asciiFact = replacements.foldLeft(fact) { case (s, (u, a)) => s.replace(u, a) }

        val qFact = Pattern.quote(fact)
        val qAscii = Pattern.quote(asciiFact)

        val quoteStart = """(?:"|`|\\<open>)\s*"""
        val quoteEnd   = """\s*(?:"|`|\\<close>)"""
        
       val fromPattern = s"""\\bfrom\\s+(?:$quoteStart)?(?:$qAscii|$qFact)(?:$quoteEnd)?\\s*""".r
        
        var newLine = fromPattern.replaceFirstIn(lineContent, "")
        if (newLine == lineContent) {
            val patternGeneral = s"""(?:$quoteStart)(?:$qAscii|$qFact)(?:$quoteEnd)""".r
            newLine = patternGeneral.replaceAllIn(lineContent, "")
        }

        newLine = newLine.replaceAll("\\s+", " ").trim
        newLine = newLine.replace("using by", "by") 
        newLine = newLine.replace("(,", "(").replace(", )", ")") 

        if (newLine != lineContent) {
            
            lines(lineNumber - 1) = newLine
            writeFile(filePath, lines.mkString("\n"))
            return true
        }
        false
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

    def processUndefined(filePath: String, lineNumber: Int, word: String): Unit = {
        val currentText = readFile(filePath)
        
        val matchedMethod = methods.find(m => word == m || word.startsWith(m + "."))
        
        val newText = if (word.endsWith("qed") && word.length > 3) {
            
            val newWord = word.stripSuffix("qed") + " qed"
            replaceWord(currentText, lineNumber, word, newWord)
        } else if (matchedMethod.isDefined) {
            replaceWord(currentText, lineNumber, word, matchedMethod.get)
        } else if (suffix.exists(s => word.endsWith("." + s))) {
            val newWord = word.split('.').head
            replaceWord(currentText, lineNumber, word, newWord)
        } else {
            val textWithoutWord = removeWord(currentText, lineNumber, word)
            val lines = textWithoutWord.split("\n", -1).toList
            lines.zipWithIndex.map {
                case (line, i) if i == lineNumber - 1 && line.contains("using by") =>
                    line.replaceFirst("""\busing\b\s*""", "").replaceAll("\\s+", " ").trim
                case (line, _) => line
            }.mkString("\n")
        }
        writeFile(filePath, newText) 
    }
}