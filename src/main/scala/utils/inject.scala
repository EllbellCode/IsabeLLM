package utils

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import scala.io.Source
import java.io.{PrintWriter, File}

object inject {

    val statementKeywords = Set("lemma", "theorem", "proposition", "corollary")
    val otherKeywords = Set("datatype", "definition", "fun", "value", "section", "record", "text", "locale", "inductive_set")
    val headerKeywords = Set("theory", "imports", "begin")

    def injectLemma(newLemma: String, filePath: String, errorLine: Int): Unit = {
        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq
        
        val searchStart = Math.max(0, errorLine - 1)

        val startOpt = (searchStart to 0 by -1).find { i =>
            val trimmed = lines(i).trim.toLowerCase
            statementKeywords.exists(kw => trimmed.startsWith(kw))
        }

        startOpt match {
            case Some(start) =>
                val end = (start + 1 until lines.length).find { i =>
                    val trimmed = lines(i).trim.toLowerCase
                    val isNewBlock = (statementKeywords ++ otherKeywords ++ Set("end")).exists(kw => trimmed.startsWith(kw))
                    isNewBlock
                }.getOrElse(lines.length)

                val updatedLines = 
                    lines.slice(0, start) ++ 
                    newLemma.stripLineEnd.split("\n") ++ 
                    lines.slice(end, lines.length)

                Files.write(Paths.get(filePath), updatedLines.mkString("\n").getBytes(StandardCharsets.UTF_8))
                println(s"Successfully injected lemma at lines $start to $end")

            case None =>
                println(s"❌ Error: Could not find a lemma/theorem keyword backwards from line $errorLine.")
        }
    }

    def injectLine(filePath: String, lineNumber: Int, newText: String): Unit = {
        val lines = Source.fromFile(filePath).getLines().toList
        if (lineNumber >= 1 && lineNumber <= lines.length) {
            val updatedLines = lines.updated(lineNumber - 1, newText)
            val writer = new PrintWriter(new File(filePath))
            updatedLines.foreach(writer.println)
            writer.close()
        } else {
            println(s"Error: Line number $lineNumber is out of bounds.")
        }
    }

    def injectAll(filePath: String, newContent: String): Unit = {
        val writer = new PrintWriter(new File(filePath))
        try {
            writer.write(newContent)
        } finally {
            writer.close()
        }
    }

    // Smart injectProof that replaces the existing proof method
    def injectProof(filePath: String, lineNumber: Int, proof: String): Unit = {
        val lines = Source.fromFile(filePath).getLines().toList
        if (lineNumber >= 1 && lineNumber <= lines.length) {
            val originalLine = lines(lineNumber - 1)

            // Matches sorry, oops, by ..., apply ... at the end of the line to replace them
            val proofTerminals = """(\s*sorry\s*$)|(\s*oops\s*$)|(\s*by\s+.*$)|(\s*apply\s+.*$)"""
            
            val cleanedLine = originalLine.replaceAll(proofTerminals, "")
            
            val updatedLine = cleanedLine + " " + proof
            
            val updatedLines = lines.updated(lineNumber - 1, updatedLine)
            val writer = new PrintWriter(new File(filePath))
            updatedLines.foreach(writer.println)
            writer.close()
        } else {
            println(s"Error: Line number $lineNumber is out of bounds.")
        }
    }
}