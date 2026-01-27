package utils

import java.io.{File, PrintWriter}
import scala.io.Source

object extract {

    val statementKeywords = Set("lemma ", "theorem ", "proposition ", "corollary ")
    val otherKeywords = Set("datatype ", "definition ", "fun ", "value ", "section", "record", "text", "locale ", "end", "inductive_set")
    val proofKeywords = List("unfolding", "using", "proof", "by", "apply", "sorry")

    // Helper to safely read a file into a list of strings
    private def readFileLines(filePath: String): IndexedSeq[String] = {
        val file = new File(filePath)
        if (!file.exists) return IndexedSeq.empty
        val source = Source.fromFile(file)
        try { source.getLines().toIndexedSeq } finally { source.close() }
    }

    def extractLineAndPath(errorMessage: String): Option[(Int, String)] = {
        val linePattern = """line (\d+)""".r
        val pathPattern = """"(.+?\.thy)"""".r

        val lineMatch = linePattern.findFirstMatchIn(errorMessage).map(_.group(1).toInt)
        val pathMatch = pathPattern.findFirstMatchIn(errorMessage).map(_.group(1))

        (lineMatch, pathMatch) match {
            case (Some(l), Some(p)) => 
                Some((l, p.replaceFirst("^~", System.getProperty("user.home"))))
            case (Some(l), None) => Some((l, "")) 
            case _ => None
        }
    }

    // FIXED: Now takes filePath (String) and reads the file, just like the old version.
    def extractStatement(filePath: String, errorLine: Int): String = {
        val lines = readFileLines(filePath)
        if (lines.isEmpty) return ""

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

    // FIXED: Now takes filePath
    def extractAll(filePath: String, errorLine: Int): String = {
        val lines = readFileLines(filePath)
        if (lines.isEmpty) return ""

        val safeErrorIndex = Math.min(errorLine - 1, lines.length - 1)

        val start = (safeErrorIndex to 0 by -1).find { i =>
            val trimmed = lines(i).trim
            statementKeywords.exists(kw => trimmed.startsWith(kw))
        }.getOrElse(0)

        val statementLines = scala.collection.mutable.ArrayBuffer[String]()
        
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

    // FIXED: Modified to work like the old one (modifying the file in place)
    def extractKeyword(filePath: String, lineNumber: Int, keyword: String): String = {
        val lines = readFileLines(filePath)
        if (lineNumber < 1 || lineNumber > lines.length) return lines.mkString("\n")

        val updatedLines = lines.updated(lineNumber - 1, {
            val line = lines(lineNumber - 1).trim
            if (line.contains(keyword)) {
                val before = line.substring(0, line.indexOf(keyword))
                if (before.contains("using")) before.substring(0, before.indexOf("using")).trim else before.trim
            } else if (line.contains("using")) {
                line.substring(0, line.indexOf("using")).trim
            } else {
                line
            }
        })
        
        // Write changes back to file (as per old functionality)
        val writer = new PrintWriter(new File(filePath))
        try { updatedLines.foreach(writer.println) } finally { writer.close() }
        
        updatedLines.mkString("\n")
    }

    // FIXED: Robust Regex to handle quotes and context
    def extractName(statement: String): String = {
        // Matches: lemma (optional context) "optional_quotes_name" : ...
        val pattern = """^\s*(?:lemma|theorem|proposition|corollary)\s+(?:\(.*\)\s+)?(?:")?([a-zA-Z0-9_]+)(?:")?.*""".r
        
        statement.linesIterator.collectFirst { 
            case pattern(name) => name 
        }.getOrElse("default_name")
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

    // FIXED: Now takes filePath
    def extractThy(filePath: String, errorLine: Int): String = {
        val lines = readFileLines(filePath)
        if (lines.isEmpty) return ""

        val safeErrorIndex = Math.min(errorLine - 1, lines.length - 1)

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
                    val beforeKeyword = trimmedLine.substring(0, keywordIndex)
                    val usingIndex = beforeKeyword.indexOf("using")
                    if (usingIndex != -1) {
                        result.append(beforeKeyword.substring(0, usingIndex).trim)
                    } else {
                        result.append(beforeKeyword.trim)
                    }
                } else {
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