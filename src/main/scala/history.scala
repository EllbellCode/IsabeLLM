import java.io.{File, PrintWriter}

// Functionality for handling the conversation history with the LLM

object history {

    def jsonCreate(lemmaName: String) = {
    
        val file = new File(s"history/$lemmaName.json")
        val writer = new PrintWriter(file)
        writer.write("[]") // Start with empty JSON array
        writer.close()
    }


               
    
}
