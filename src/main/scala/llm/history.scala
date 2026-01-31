package llm

import java.io.{File, PrintWriter}

object history {

    // Creates a json file for the llm dialogue of a given lemma
    // Note: This truncates the file, but getRunHistoryPath guarantees we are passing a new, non-existent file path.
    def jsonCreate(path: String) = {
        val file = new File(path)
        if (file.getParentFile != null) file.getParentFile.mkdirs()
        
        val writer = new PrintWriter(file)
        writer.write("[]") // Start with empty JSON array
        writer.close()
    }

    // UPDATED: Now ensures uniqueness to prevent overwriting previous runs
    def getRunHistoryPath(dir: String, lemmaName: String, runId: Int): String = {
        val folder = new File(dir)
        if (!folder.exists()) folder.mkdirs()

        val baseName = s"${lemmaName}_run_$runId"

        // Helper to generate candidate paths:
        // 0 -> history/lemma_run_1.json
        // 1 -> history/lemma_run_1_1.json
        // 2 -> history/lemma_run_1_2.json
        def buildPath(index: Int): String = {
            val fileName = if (index == 0) s"$baseName.json" else s"${baseName}_$index.json"
            s"$dir/$fileName"
        }

        var i = 0
        var candidatePath = buildPath(i)

        // Loop until we find a filename that does NOT exist
        while (new File(candidatePath).exists()) {
            i += 1
            candidatePath = buildPath(i)
        }

        candidatePath
    }         
}
