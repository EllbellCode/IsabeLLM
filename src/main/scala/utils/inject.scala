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
    
    // NEW: Extracts the raw string of facts, preserving structure like brackets [OF ...]
    // Stops at 'unfolding', 'by', or 'apply' to avoid capturing keywords as facts.
    private def extractRawFacts(text: String): Option[String] = {
        val pattern = """\busing\s+(.*?)\s*(?=\bby\b|\bapply\b|\bunfolding\b|$)""".r
        pattern.findFirstMatchIn(text).map(_.group(1).trim)
    }

    // NEW: Extracts simple tokenized facts (safe for Sledgehammer output which is usually simple)
    private def extractSimpleFacts(text: String): Set[String] = {
        extractRawFacts(text) match {
            case Some(raw) => raw.split("\\s+").map(_.trim).filter(_.nonEmpty).toSet
            case None => Set.empty
        }
    }
    
    def injectProof(filePath: String, lineNumber: Int, proof: String): Unit = {
        val lines = Source.fromFile(filePath).getLines().toList
        if (lineNumber >= 1 && lineNumber <= lines.length) {
            val originalLine = lines(lineNumber - 1)
            var finalProof = proof

            // Merge Logic: If both lines use "using", preserve the old complex facts and add new unique ones.
            if (proof.trim.startsWith("using") && originalLine.contains("using")) {
                 
                 val originalRawOpt = extractRawFacts(originalLine)
                 val newSimpleFacts = extractSimpleFacts(proof)
                 
                 if (originalRawOpt.isDefined) {
                     val baseFacts = originalRawOpt.get
                     
                     // Filter out new facts that are already present in the base string.
                     // We use word boundaries (\b) to ensure "x" doesn't match inside "max" or "ex".
                     val factsToAdd = newSimpleFacts.filterNot { f =>
                         val escaped = java.util.regex.Pattern.quote(f)
                         s"\\b$escaped\\b".r.findFirstIn(baseFacts).isDefined
                     }
                     
                     if (factsToAdd.nonEmpty) {
                        println(s"   -> Merging facts: '$baseFacts' + [${factsToAdd.mkString(", ")}]")
                        
                        val mergedFacts = baseFacts + " " + factsToAdd.mkString(" ")
                        
                        // Extract the method part from the NEW proof (stripping the 'using ...' prefix)
                        // We use the same regex logic to ensure we strip exactly what we extracted.
                        val newMethodPart = proof.replaceFirst("""\busing\s+.*?(?=\bby\b|\bapply\b|\bunfolding\b|$)""", "").trim
                        
                        finalProof = s"using $mergedFacts $newMethodPart"
                     }
                 }
            }

            // Cleanup: remove old proof terminators
            val proofTerminals = """(\s*\b(sorry|oops)\b[\s\S]*$)|(\s*\b(by|apply)\b[\s\S]*$)|(\s*(\.\.|\.)\s*$)"""
            var cleanedLine = originalLine.replaceAll(proofTerminals, "")
            
            // If the final proof has "using", strip any "using" from the original line prefix to avoid duplication.
            if (finalProof.trim.startsWith("using")) {
                cleanedLine = cleanedLine.replaceAll("""\s+\busing\b[\s\S]*$""", "")
            }
            
            val updatedLine = cleanedLine + " " + finalProof
            
            val updatedLines = lines.updated(lineNumber - 1, updatedLine)
            val writer = new PrintWriter(new File(filePath))
            updatedLines.foreach(writer.println)
            writer.close()
        } else {
            println(s"Error: Line number $lineNumber is out of bounds.")
        }
    }
}