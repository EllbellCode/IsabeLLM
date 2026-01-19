
package utils

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import scala.io.Source
import java.io.{PrintWriter, File}

object inject {

    // Added more keywords and made them regex-ready
    val statementKeywords = Set("lemma", "theorem", "proposition", "corollary")
    val otherKeywords = Set("datatype", "definition", "fun", "value", "section", "record", "text", "locale", "inductive_set")
    val headerKeywords = Set("theory", "imports", "begin")

    def injectLemma(newLemma: String, filePath: String, errorLine: Int): Unit = {
        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq
        
        // Ensure we don't start at a negative index if errorLine is 0
        val searchStart = Math.max(0, errorLine - 1)

        // 1. Find the start of the lemma (search backwards)
        val startOpt = (searchStart to 0 by -1).find { i =>
            val trimmed = lines(i).trim.toLowerCase
            statementKeywords.exists(kw => trimmed.startsWith(kw))
        }

        startOpt match {
            case Some(start) =>
                // 2. Find the end of the block (search forwards)
                // We look for the NEXT top-level keyword or the end of the file
                val end = (start + 1 until lines.length).find { i =>
                    val trimmed = lines(i).trim.toLowerCase
                    val isNewBlock = (statementKeywords ++ otherKeywords ++ Set("end")).exists(kw => trimmed.startsWith(kw))
                    isNewBlock
                }.getOrElse(lines.length)

                // 3. Construct the updated content
                val updatedLines = 
                    lines.slice(0, start) ++ 
                    newLemma.stripLineEnd.split("\n") ++ 
                    lines.slice(end, lines.length)

                Files.write(Paths.get(filePath), updatedLines.mkString("\n").getBytes(StandardCharsets.UTF_8))
                println(s"Successfully injected lemma at lines $start to $end")

            case None =>
                println(s"❌ Error: Could not find a lemma/theorem keyword backwards from line $errorLine.")
                if (lines.indices.contains(errorLine - 1)) 
                    println(s"Line $errorLine content: ${lines(errorLine - 1)}")
        }
    }

    // Injects a new line in place of the given line
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

    // Rewrites a whole file with the newContent
    def injectAll(filePath: String, newContent: String): Unit = {
        val writer = new PrintWriter(new File(filePath))
        try {
            writer.write(newContent)
        } finally {
            writer.close()
        }
    }

    // MODIFIED: Smart injectProof that replaces the existing proof method
    def injectProof(filePath: String, lineNumber: Int, proof: String): Unit = {
        val lines = Source.fromFile(filePath).getLines().toList
        if (lineNumber >= 1 && lineNumber <= lines.length) {
            val originalLine = lines(lineNumber - 1)

            // Regex explanation:
            // \s* -> Matches optional whitespace
            // (sorry|...) -> Matches specific keywords: sorry, oops
            // |         -> OR
            // (by\s+.*) -> Matches 'by' followed by spaces and any text until the end
            // (apply\s+.*) -> Matches 'apply' followed by spaces and any text (careful usage)
            // $         -> Ensures it matches at the very end of the line
            val proofTerminals = """(\s*sorry\s*$)|(\s*oops\s*$)|(\s*by\s+.*$)|(\s*apply\s+.*$)"""
            
            // Remove the old failing method
            val cleanedLine = originalLine.replaceAll(proofTerminals, "")
            
            // Append the new proof (ensure exactly one space separator)
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