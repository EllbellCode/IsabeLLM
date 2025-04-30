//FUNCTIONALITY FOR DEALING WITH BUILD TIMEOUTS

import scala.io.Source


object timeout {

    val statementKeywords = Set(
        "lemma ", "theorem ", "proposition ", "corollary "
    )

    val otherKeywords = Set(
        "datatype ", "definition ", "fun ", "value ", "section", "record", "text", "locale ", "end", "inductive_set"
    )

    val tacticKeywords = Set(
        "blast", "metis"
    )

    // Returns the Line of the first occurence of the inputted string
    // When looking for a lemma, the first occurence will be the lemma statement! **************************************
    def findLines(filePath: String, lemmaName: String): (Int, Int) = {
        val lines = Source.fromFile(filePath).getLines().toList

        // Find the line number of the lemma
        val lemmaLineOpt = lines.zipWithIndex.find {
            case (line, _) => line.contains(lemmaName)
        }.map(_._2)

        // If lemma is found
        lemmaLineOpt match {
            case Some(lemmaLine) =>
                // Iterate over subsequent lines to find the last line of the proof
                val proofEndLine = lines.drop(lemmaLine + 1).zipWithIndex.collectFirst {
                    case (line, index) if statementKeywords.exists(line.contains) || otherKeywords.exists(line.contains) =>
                        lemmaLine + 1 + index
                }

                // Return the lemma line and the last line of the proof
                proofEndLine match {
                    case Some(endLine) => (lemmaLine, endLine)
                    case None => (lemmaLine, lines.size - 1) // If no end line found, return the last line of the file
                }

            case None =>
                // Return (-1, -1) if lemma is not found
                (-1, -1)
        }
    }

    def removeTactics(input: String): String = {
        val keywords = Seq("using", "by")

        val cleanedLines = input.linesIterator.map { line =>
            val lowerLine = line.toLowerCase
            val hasUnsafeTactic =
                tacticKeywords.exists(kw => lowerLine.contains(kw)) &&
                !lowerLine.contains("safe")

            if (hasUnsafeTactic) {
            val keywordIndex = keywords
                .map(kw => lowerLine.indexOf(kw))
                .filter(_ != -1)
                .sorted
                .headOption

            keywordIndex match {
                case Some(idx) => line.substring(0, idx).trim
                case None      => line
            }
            } else {
                line
            }
        }
        cleanedLines.mkString("\n")
    }

    def tacticSearch(filePath: String, start: Int, end: Int): Int = {
        val lines = Source.fromFile(filePath).getLines().toList

        // Iterate over the specified range and find the first line containing "blast" or "metis"
        (start to end).collectFirst {
            case i if tacticKeywords.exists(kw => lines(i).toLowerCase.contains(kw)) => i
        }.getOrElse(-1) // Return -1 if not found
    }
}