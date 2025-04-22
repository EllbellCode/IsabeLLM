import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import scala.io.Source
import java.io.{PrintWriter, File}

// Functionality for injecting information into a .thy file

object inject {

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
    

    def injectLemma(newLemma: String, filePath: String, errorLine: Int): Unit = {

        val lines = scala.io.Source.fromFile(filePath).getLines().toIndexedSeq

        // Find the start line (first line with a statement keyword)
        val start = (errorLine - 1 to 0 by -1).find { i =>
            val trimmed = lines(i).trim
            statementKeywords.exists(kw => trimmed.startsWith(kw))
        }.getOrElse(0)

        // Find the end of the block (where a new top-level keyword appears)
        val end = (start + 1 until lines.length).find { i =>
            val trimmed = lines(i).trim
            val isNewTopLevel =
                (statementKeywords.exists(kw => trimmed.startsWith(kw)) && i != start) ||
                otherKeywords.exists(kw => trimmed.startsWith(kw))
            isNewTopLevel
        }.getOrElse(lines.length)

        // Create a new version of the file content with the lemma replaced
        val updatedLines =
            lines.slice(0, start) ++
            newLemma.stripLineEnd.split("\n") ++
            lines.slice(end, lines.length)

        // Write the updated content back to the file
        Files.write(Paths.get(filePath), updatedLines.mkString("\n").getBytes(StandardCharsets.UTF_8))
    }

    def injectLine(filePath: String, lineNumber: Int, newText: String): Unit = {
        // Read all lines from the file
        val lines = Source.fromFile(filePath).getLines().toList

        // Check if the lineNumber is valid
        if (lineNumber >= 1 && lineNumber <= lines.length) {
            // Modify the specific line
            val updatedLines = lines.updated(lineNumber - 1, newText)

            // Write the updated content back to the file
            val writer = new PrintWriter(new File(filePath))
            updatedLines.foreach(writer.println)
            writer.close()
        } else {
            println(s"Error: Line number $lineNumber is out of bounds.")
        }
    }
}