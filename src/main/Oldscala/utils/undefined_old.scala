
package utils

import java.io.PrintWriter
import scala.io.Source
import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets


object undefined {
    
     val methods = Set(
        "Cons"
    )

    val syntax = Set(
        "using by"
    )

    val suffix = Set(
        "IH"
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

        val pattern = ("""(\s*|;)""" + java.util.regex.Pattern.quote(word) + """(\[[^\]]*\])?""").r

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

    // removes incorrect use of "Using" keyword
    def removeUsing(filePath: String, lineNumber: Int): Unit = {
        val expandedPath = filePath.replaceFirst("^~", System.getProperty("user.home"))
        val source = scala.io.Source.fromFile(expandedPath)
        val lines = source.getLines().toList
        source.close()

        val idx = lineNumber - 1
        val updatedLines = lines.zipWithIndex.map {
            case (line, i) if i == idx && line.contains("using by") =>
                // Remove "using" when followed by "by", keeping spacing clean
                line.replaceFirst("""\busing\b\s*""", "").replaceAll("\\s+", " ").trim
            case (line, _) => line
        }

        val writer = new PrintWriter(expandedPath)
        updatedLines.foreach(writer.println)
        writer.close()
    }

    def removeTHM0(input: String): String = {
        
        val pattern = """\b\w+\[[^\[\]]*\]""".r
        
        pattern.replaceAllIn(input, m => {
            val word = m.matched.takeWhile(_ != '[')
            word
        }
        )
    }

    // Checks if the undefined word is a derivative of a commom Isabelle method
    // Returns the method if it is ***********************************************************
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

    // applies all of the above
    def processUndefined(filePath: String, lineNumber: Int, word: String): Unit = {

        if (methods.exists(word.contains)) {
            println("Modifying method...")
            val newWord = checkUndefined(word)
            replaceWord(filePath, lineNumber, word, newWord)
        } else if (suffix.exists(s => word.endsWith("." + s))) {

            println("Removing suffix...")
            val newWord = removeSuffix(word)
            replaceWord(filePath, lineNumber, word, newWord)

        } else {
            println("Removing method...")
            removeWord(filePath, lineNumber, word)
            removeUsing(filePath, lineNumber)
        }
    }
    
}