package utils

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import scala.io.Source
import java.io.{PrintWriter, File}
import scala.util.matching.Regex

object inject {

    val statementKeywords = Set("lemma", "theorem", "proposition", "corollary")
    val otherKeywords = Set("datatype", "definition", "fun", "value", "section", "record", "text", "locale", "inductive_set")
    val headerKeywords = Set("theory", "imports", "begin")

    // Regex to tokenize facts while respecting quotes, cartouches, and backticks.
    private val factTokenizer = """(\\<open>[\s\S]*?\\<close>|"[^"]*"|`[^`]*`|[^\s]+)""".r

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

                val writer = new PrintWriter(new File(filePath))
                try {
                    updatedLines.foreach(writer.println)
                } finally {
                    writer.close()
                }

                println(s"Successfully injected lemma at lines ${start + 1} to ${end}")

            case None =>
                println("Error: Could not find start of lemma block.")
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
    
    // Parses a string of facts into a Set of individual facts
    private def parseFactsSafe(text: String): Set[String] = {
        factTokenizer.findAllIn(text).toSet
    }

    def injectProof(filePath: String, lineNumber: Int, proof: String): Unit = {
        val lines = Source.fromFile(filePath).getLines().toList
        if (lineNumber >= 1 && lineNumber <= lines.length) {
            val originalLine = lines(lineNumber - 1)
            
            // UPDATED REGEX: 
            // Now includes \.\. (double dot), \. (dot), sorry, and oops in the capture group.
            // This ensures they are recognized as the 'method' part and stripped out.
            val lineParser = """^(\s*)(.*?)(\s+using\s+[\s\S]+?)?(\s*(?:by|apply|unfolding|proof|sorry|oops|\.\.|\.)\b[\s\S]*)?$""".r

            val proofParser = """^(?:using\s+([\s\S]+?))?\s*((?:by|apply|unfolding|proof)\b[\s\S]*)?$""".r

            val newLine = originalLine match {
                case lineParser(indent, command, existingUsingRaw, existingMethod) =>
                    
                    val existingFactsStr = if (existingUsingRaw != null) existingUsingRaw.trim.stripPrefix("using").trim else ""
                    val existingFacts = if (existingFactsStr.nonEmpty) parseFactsSafe(existingFactsStr) else Set.empty[String]

                    val (newFacts, newMethodPart) = proof.trim match {
                        case proofParser(newUsingStr, methodStr) =>
                            val nf = if (newUsingStr != null) parseFactsSafe(newUsingStr) else Set.empty[String]
                            val nm = if (methodStr != null) methodStr.trim else ""
                            (nf, nm)
                        case _ => (Set.empty[String], proof.trim) 
                    }

                    // Merge facts
                    val mergedFacts = existingFacts ++ newFacts
                    val finalUsing = if (mergedFacts.nonEmpty) " using " + mergedFacts.mkString(" ") else ""
                    
                    // Determine the final method part. 
                    // If the new proof has a method, use it. Otherwise fallback to existing (unless existing was a dot, in which case we might have issues if new proof has no method, but sledgehammer usually provides 'by ...')
                    val finalMethod = if (newMethodPart.nonEmpty) newMethodPart else if (existingMethod != null) existingMethod.trim else ""
                    
                    s"$indent$command$finalUsing $finalMethod"

                case _ => 
                    if (originalLine.trim.nonEmpty) s"$originalLine $proof" else proof
            }

            val cleanedLine = newLine.replaceAll(" +", " ").trim
            val finalLine = originalLine.takeWhile(_.isWhitespace) + cleanedLine

            val updatedLines = lines.updated(lineNumber - 1, finalLine)
            val writer = new PrintWriter(new File(filePath))
            try {
                updatedLines.foreach(writer.println)
            } finally {
                writer.close()
            }
        } else {
            println(s"Error: Line number $lineNumber is out of bounds.")
        }
    }
}