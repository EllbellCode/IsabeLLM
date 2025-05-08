//FUNCTIONALITY FOR DEALING WITH ISABELLE BUILD TIMEOUTS

import scala.io.Source
import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets

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
    // Also returns the end line of the proof
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

    // Returns the first line where a potentiial unsafe tactic appears
    def tacticSearch(filePath: String, start: Int, end: Int): Int = {
        val lines = Source.fromFile(filePath).getLines().toList

        (start to end).collectFirst {
            case i if tacticKeywords.exists(kw => lines(i).toLowerCase.contains(kw)) => i
        }.getOrElse(-1) // Return -1 if not found
    }

    // places "using assms" at the start of the proof to amend incorect use
    def assmsFix(filePath: String, lemmaName: String): Boolean = {
        val (startLine, endLine) = findLines(filePath, lemmaName)
        if (startLine == -1 || endLine == -1) {
            println(s"Lemma '$lemmaName' not found in $filePath")
            return false
        }

        val lines = Source.fromFile(filePath).getLines().toList

        val proofStartIdx = (startLine to endLine).find(i => lines(i).trim.startsWith("proof")).getOrElse(-1)
        if (proofStartIdx == -1) {
            println(s"No 'proof' keyword found for lemma '$lemmaName'")
            return false
        }

        val beforeLemma  = lines.take(startLine)
        val lemmaSection = lines.slice(startLine, endLine + 1)
        val afterLemma   = lines.drop(endLine + 1)

        var changed = false

        val proofLineRelIdx = proofStartIdx - startLine

        // Check if 'using assms' is already directly before proof
        val alreadyCorrect = 
            proofLineRelIdx > 0 && lemmaSection(proofLineRelIdx - 1).trim == "using assms"

        // Remove all incorrect uses of 'using assms'
        val cleanedLemmaSection = lemmaSection.zipWithIndex.map {
            case (line, relIdx) =>
                val absIdx = startLine + relIdx
                val isBeforeProof = relIdx == proofLineRelIdx - 1
                if (!isBeforeProof && line.contains("using assms")) {
                    changed = true
                    line.replace("using assms", "").replaceAll("""\s+by""", " by").trim
                } else {
                    line
                }
        }

        // Inject 'using assms' before proof only if not already there
        val finalLemmaSection =
            if (!alreadyCorrect) {
                changed = true
                cleanedLemmaSection.patch(proofLineRelIdx, Seq("using assms", cleanedLemmaSection(proofLineRelIdx)), 1)
            } else {
                cleanedLemmaSection
            }

        if (changed) {
            val newLines = beforeLemma ++ finalLemmaSection ++ afterLemma
            Files.write(Paths.get(filePath), newLines.mkString("\n").getBytes(StandardCharsets.UTF_8))
            println(s"Rewritten 'using assms' in $filePath for lemma '$lemmaName'")
            return true
        } else {
            return false
        }
    }
}