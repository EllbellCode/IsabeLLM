
package llm

// Functionality for handling the conversation history with the LLM

import java.io.{File, PrintWriter}

object history {

    // Creates a json file for the llm dialogue of a given lemma
    def jsonCreate(lemmaName: String) = {
    
        val file = new File(s"history/$lemmaName.json")
        val writer = new PrintWriter(file)
        writer.write("[]") // Start with empty JSON array
        writer.close()
    }

    // makes a new json file if a json for the same lemma from
    // a previous isabellm call exists
    def getUniqueJsonPath(dir: String, baseName: String): String = {
        val folder = new File(dir)
        if (!folder.exists()) folder.mkdirs()

        val existingFiles = folder.listFiles().map(_.getName).toSet

        def buildPath(index: Int): String = {
            val name = if (index == 0) s"$baseName.json" else s"${baseName}${index}.json"
            s"$dir/$name"
        }

        var i = 0
        var newPath = buildPath(i)
        while (existingFiles.contains(new File(newPath).getName)) {
            i += 1
            newPath = buildPath(i)
        }

        newPath
    }         
    
}
