import java.io.File
import scala.io.Source
import java.io.PrintWriter


// Functionality for extracting information from a .thy file
// Using data from error messages when running isabelle build

object extract {

    val statementKeywords = Set(
        "lemma ", "theorem ", "proposition ", "corollary "
    )

    val otherKeywords = Set(
        "datatype ", "definition ", "fun ", "value ", "section", "record", "text", "locale ", "end", "inductive_set"
    )

    val proofKeywords = List(
        "unfolding ", "using ", "proof", "by ", "apply", "sorry "
    )

    val intermediateKeywords = Set(
    "hence ", "thus ", "obtain ", "show ", "ultimately ", "moreover ", "then "
    )
    
    // Extracts the path to the file that produced the error
    // And the line number the error took place *************************************************************
    def extractLineAndPath(errorMessage: String): Option[(Int, String)] = {
        val pattern = """line (\d+) of "(.+?\.thy)"""".r

        val matches = pattern.findAllMatchIn(errorMessage).map { m =>
            val lineNumber = m.group(1).toInt
            val rawPath = m.group(2)
            val fullPath = if (rawPath.startsWith("~")) {
            rawPath.replaceFirst("^~", System.getProperty("user.home"))
            } else {
            rawPath
            }
            (lineNumber, fullPath)
        }.toList

        matches.sortBy(_._1).headOption
    }

    // Extracts everything within a Statement
    // Includes the Statement name, the statement itself, and the proof of the statement******************
    def extractAll(filePath: String, errorLine: Int): String = {

        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq

        // 1. Find the start line (first line with a statement keyword)
        val start = (errorLine - 1 to 0 by -1).find { i =>
        val trimmed = lines(i).trim
        statementKeywords.exists(kw => trimmed.startsWith(kw))
        }.getOrElse(0)

        val statementLines = scala.collection.mutable.ArrayBuffer[String]()
        // 2. Collect lines until another top-level keyword is found
        for (i <- start until lines.length) {
            val trimmed = lines(i).trim

            val isNewTopLevel =
                statementKeywords.exists(kw => trimmed.startsWith(kw)) && i != start || 
                otherKeywords.exists(kw => trimmed.startsWith(kw))

            if (isNewTopLevel) {
                // Stop before the new block
                return statementLines.mkString("\n")
            }   else {
                    statementLines.append(lines(i))
                }
        }

        statementLines.mkString("\n")
    }
    
    // Extracts everything in the .thy file before the Statement we are working on************************
    def extractThy(filePath: String, errorLine: Int): String = {
        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq

        // 1. Find the start line (first line with a statement keyword)
        val start = (errorLine - 1 to 0 by -1).find { i =>
            val trimmed = lines(i).trim
            statementKeywords.exists(kw => trimmed.startsWith(kw))
        }.getOrElse(0)

        // 2. Collect all lines before the start of the statement
        val linesBeforeStatement = lines.take(start)

        // 4. Return everything before the statement
        linesBeforeStatement.mkString("\n")
    }

    //Extracts the line  from the file
    def extractLine(filePath: String, errorLine: Int): String = {

        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq

        if (errorLine >= 1 && errorLine <= lines.length) lines(errorLine - 1)
        else ""
    }

    // Returns the name of Statement
    // Use on the output of extractStatement! ********************************************************** 
    def extractName(statement: String): String = {
        val keywords = Set("lemma", "theorem", "proposition", "corollary")
        val keywordPattern = keywords.mkString("|")
        val pattern = s"""^\\s*($keywordPattern)\\s+(\\w+).*""".r

        statement.linesIterator.collectFirst {
            case pattern(_, name) => name
        }.getOrElse("default_name")
    }

    // Extracts everything from a thy file ***********************************************************
    def extractText(filePath: String): String = {
        val file = new File(filePath)

        if (!file.exists || !file.getName.endsWith(".thy")) {
            throw new IllegalArgumentException(s"Invalid file: $filePath")
        }

        val source = Source.fromFile(file)
        try {
            source.getLines().mkString("\n")
        } finally {
            source.close()
        }
    }

    // Extract the command from an error message *****************************************************
    def extractCommand(errorMessage: String): String = {
        val pattern = """At command "([^"]+)"""".r
        pattern.findFirstMatchIn(errorMessage) match {
            case Some(m) => m.group(1)
            case None => ""
        }
    }

    // EXTRACTS A FILE UP TO THE SPECIFIED LINE BUT ONLY EVERYTHING BEFORE THE SPECIFIED KEYWORD *************************
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

    // REMOVES EVERYTHING INLCUDING AND AFTER A KEYWORD IN A SPECIFIED FILE LINE ****************************************** 
    def extractKeyword(filePath: String, lineNumber: Int, keyword: String): Unit = {
        val lines = Source.fromFile(filePath).getLines().toList

        val updatedLines = lines.zipWithIndex.map {
            case (line, idx) if idx + 1 == lineNumber =>
            val trimmedLine = line.trim
            val keywordIndex = trimmedLine.indexOf(keyword)

            if (keywordIndex != -1) {
                val beforeKeyword = trimmedLine.substring(0, keywordIndex)
                val usingIndex = beforeKeyword.indexOf("using")
                if (usingIndex != -1)
                beforeKeyword.substring(0, usingIndex).trim
                else
                beforeKeyword.trim
            } else {
                val usingIndex = trimmedLine.indexOf("using")
                if (usingIndex != -1)
                trimmedLine.substring(0, usingIndex).trim
                else
                trimmedLine
            }

            case (line, _) => line
        }

        val writer = new PrintWriter(filePath)
        try {
            updatedLines.foreach(writer.println)
        } finally {
            writer.close()
        }
    }

}