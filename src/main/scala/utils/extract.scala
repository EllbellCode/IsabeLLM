package utils

import java.io.File
import scala.io.Source

object extract {

    val statementKeywords = Set("lemma ", "theorem ", "proposition ", "corollary ")
    val otherKeywords = Set("datatype ", "definition ", "fun ", "value ", "section", "record", "text", "locale ", "end", "inductive_set")
    val proofKeywords = List("unfolding", "using", "proof", "by", "apply", "sorry")

    // Extracts line and path from error message (unchanged as it parses the error string)
    def extractLineAndPath(errorMessage: String): Option[(Int, String)] = {
        
        val linePattern = """line (\d+)""".r
        val pathPattern = """"(.+?\.thy)"""".r

        val lineMatch = linePattern.findFirstMatchIn(errorMessage).map(_.group(1).toInt)
        val pathMatch = pathPattern.findFirstMatchIn(errorMessage).map(_.group(1))

        (lineMatch, pathMatch) match {
            case (Some(l), Some(p)) => 
                Some((l, p.replaceFirst("^~", System.getProperty("user.home"))))
            case (Some(l), None) => 
                // If path is missing, we at least have the line number
                Some((l, "")) 
            case _ => None
        }
    }

    def extractStatement(theoryText: String, errorLine: Int): String = {
        val lines = theoryText.split("\n", -1).toIndexedSeq
        val start = (errorLine - 1 to 0 by -1).find { i =>
            val trimmed = lines(i).trim
            statementKeywords.exists(kw => trimmed.startsWith(kw))
        }.getOrElse(0)

        val statementLines = scala.collection.mutable.ArrayBuffer[String]()
        var reachedProof = false

        for (i <- start until lines.length if !reachedProof) {
            val line = lines(i).trim
            val proofIdx = findFirstKeywordOutsideQuotes(line)
            proofIdx match {
                case Some((_, 0)) if line.nonEmpty => reachedProof = true
                case Some((_, idx)) =>
                    val truncated = lines(i).substring(0, idx).trim
                    if (truncated.nonEmpty) statementLines.append(truncated)
                    reachedProof = true
                case None => statementLines.append(lines(i))
            }
        }
        statementLines.mkString("\n")
    }

    private def findFirstKeywordOutsideQuotes(line: String): Option[(String, Int)] = {
        var inQuotes = false
        for (i <- 0 until line.length) {
            if (line.charAt(i) == '"') inQuotes = !inQuotes
            else if (!inQuotes) {
                for (kw <- proofKeywords) {
                    if (line.startsWith(kw, i) && (i == 0 || line.charAt(i - 1).isWhitespace)) return Some((kw, i))
                }
            }
        }
        None
    }

    def extractAll(filePath: String, errorLine: Int): String = {
      
        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq
        if (lines.isEmpty) return "" // Handle empty file

        // Ensure errorLine doesn't exceed bounds
        val safeErrorIndex = Math.min(errorLine - 1, lines.length - 1)

        // 1. Find the start line safely
        val start = (safeErrorIndex to 0 by -1).find { i =>
            val trimmed = lines(i).trim
            statementKeywords.exists(kw => trimmed.startsWith(kw))
        }.getOrElse(0)

        val statementLines = scala.collection.mutable.ArrayBuffer[String]()
        
        // 2. Collect lines safely
        for (i <- start until lines.length) {
            val trimmed = lines(i).trim
            val isNewTopLevel =
                (statementKeywords.exists(kw => trimmed.startsWith(kw)) && i != start) || 
                otherKeywords.exists(kw => trimmed.startsWith(kw))

            if (isNewTopLevel) {
                return statementLines.mkString("\n")
            } else {
                statementLines.append(lines(i))
            }
        }
        statementLines.mkString("\n")
    }

    def extractKeyword(theoryText: String, lineNumber: Int, keyword: String): String = {
        val lines = theoryText.split("\n", -1).toIndexedSeq
        if (lineNumber < 1 || lineNumber > lines.length) return theoryText

        val updatedLine = lines(lineNumber - 1).trim match {
            case line if line.contains(keyword) =>
                val before = line.substring(0, line.indexOf(keyword))
                if (before.contains("using")) before.substring(0, before.indexOf("using")).trim else before.trim
            case line if line.contains("using") => line.substring(0, line.indexOf("using")).trim
            case line => line
        }
        lines.updated(lineNumber - 1, updatedLine).mkString("\n")
    }

    def extractName(statement: String): String = {
        val pattern = """^\s*(?:lemma|theorem|proposition|corollary)\s+(\w+).*""".r
        statement.linesIterator.collectFirst { case pattern(name) => name }.getOrElse("default_name")
    }

    def extractText(filePath: String): String = {
        val source = Source.fromFile(new File(filePath))
        try { source.getLines().mkString("\n") } finally { source.close() }
    }

    def extractCommand(errorMessage: String): String = 
        """At command "([^"]+)"""".r.findFirstMatchIn(errorMessage).map(_.group(1)).getOrElse("")

    def extractLine(filePath: String, lineNum: Int): String = {
        val source = scala.io.Source.fromFile(filePath)
        try {
            source.getLines().drop(lineNum - 1).next()
        } finally {
            source.close()
        }
    }

    def extractThy(filePath: String, errorLine: Int): String = {
      
        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq
        if (lines.isEmpty) return "" // Handle empty file

        // Ensure errorLine doesn't exceed bounds
        val safeErrorIndex = Math.min(errorLine - 1, lines.length - 1)

        // Find the start line safely
        val start = (safeErrorIndex to 0 by -1).find { i =>
            val trimmed = lines(i).trim
            statementKeywords.exists(kw => trimmed.startsWith(kw))
        }.getOrElse(0)

        val linesBeforeStatement = lines.take(start)
        linesBeforeStatement.mkString("\n")
    }

    def extractToKeyword(filePath: String, lineNumber: Int, keyword: String): String = {
        val source = Source.fromFile(filePath)
        val result = new StringBuilder

        try {
            for ((line, idx) <- source.getLines().zipWithIndex) {
            if (idx + 1 == lineNumber) {
                val trimmedLine = line.trim
                val keywordIndex = trimmedLine.indexOf(keyword)

                if (keywordIndex != -1) {
                // Slice up to keyword first
                val beforeKeyword = trimmedLine.substring(0, keywordIndex)

                // Then check if "using" appears before the keyword
                val usingIndex = beforeKeyword.indexOf("using")

                // If "using" exists before keyword, cut at "using"
                if (usingIndex != -1) {
                    result.append(beforeKeyword.substring(0, usingIndex).trim)
                } else {
                    result.append(beforeKeyword.trim)
                }
                } else {
                // If keyword isn't found, still cut at "using" if present
                val usingIndex = trimmedLine.indexOf("using")
                if (usingIndex != -1) {
                    result.append(trimmedLine.substring(0, usingIndex).trim)
                } else {
                    result.append(trimmedLine)
                }
                }

                return result.toString().stripTrailing()
            }

            result.append(line).append("\n")
            }
        } finally {
            source.close()
        }

        result.toString().stripTrailing()
    }
}