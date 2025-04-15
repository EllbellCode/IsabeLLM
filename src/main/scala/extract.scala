

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
    

    def extractStatement(filePath: String, errorLine: Int): String = {
        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq

        // 1. Find the start line (first line with a statement keyword)
        val start = (errorLine - 1 to 0 by -1).find { i =>
        val trimmed = lines(i).trim
        statementKeywords.exists(kw => trimmed.startsWith(kw))
        }.getOrElse(0)

        // 2. Iterate forwards until we encounter a line with proof-starting keyword
        val statementLines = scala.collection.mutable.ArrayBuffer[String]()
        var reachedProof = false

        for (i <- start until lines.length if !reachedProof) {
            val line = lines(i)

            // If line contains a proof keyword, truncate it
            proofKeywords.find(line.contains) match {
                case Some(keyword) =>
                val truncated = line.substring(0, line.indexOf(keyword)).trim
                if (truncated.nonEmpty) statementLines.append(truncated)
                reachedProof = true
                case None =>
                statementLines.append(line)
            }
        }

        statementLines.mkString("\n")
    }

    def extractLineAndPath(errorMessage: String): Option[(Int, String)] = {
        val pattern = """line (\d+) of "(.+?\.thy)"""".r

        pattern.findFirstMatchIn(errorMessage).map { m =>
            val lineNumber = m.group(1).toInt
            val rawPath = m.group(2)
            val fullPath = if (rawPath.startsWith("~")) {
            rawPath.replaceFirst("^~", System.getProperty("user.home"))
            } else {
            rawPath
            }
            (lineNumber, fullPath)
        }
        }

    def extractIntermediate(filePath: String, errorLine: Int): String = {
        
        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq

        val start = (errorLine -1 to 0 by -1).find {i =>
            val trimmed = lines(i).trim
            intermediateKeywords.exists(kw => trimmed.startsWith(kw))
        }.getOrElse(0)

        val intermediate = scala.collection.mutable.ArrayBuffer[String]()
        var reachedProof = false 
        
        for (i <- start until lines.length if !reachedProof) {
            val line = lines(i)

            proofKeywords.find(line.contains) match {
                case Some(keyword) =>
                val truncated = line.substring(0, line.indexOf(keyword)).trim
                if (truncated.nonEmpty) intermediate.append(truncated)
                reachedProof = true
                case None =>
                intermediate.append(line)
            }    
        }

        intermediate.mkString("\n")
    }

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

    def extractLine(filePath: String, errorLine: Int): String = {

        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq

        if (errorLine >= 1 && errorLine <= lines.length) lines(errorLine - 1)
        else ""
    }
}