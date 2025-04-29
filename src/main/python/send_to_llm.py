import os
import sys
from openai import OpenAI
import json

preamble = "I am trying to complete a proof in Isabelle. Here is my theory file so far:"
lemma_proof = "I am trying to prove the following lemma:"
request = "Please prove this lemma. " \
          "Return only the raw code without any additional text, explanations, formatting, or commentary." \
          "Do not include ``` or language tags. Just the pure code."

fail_return = "Your proof is incorrect. The current proof state is:"
line_error = "The line: "
error_message = "produced the following error message:"
error_request = "Please amend the proof to deal with this error." \
                "Return only the raw code without any additional text, explanations, formatting, or commentary."\
                "Do not include ``` or language tags. Just the pure code."

key = os.getenv("openai_key")

# Initialize client
client = OpenAI(
    base_url="https://openrouter.ai/api/v1",
    api_key= key
)

def query_llm(prompt: str, history: list) -> tuple[str, list]:
    
    history.append({"role": "user", "content": prompt})
    
    response = client.chat.completions.create(
        model="deepseek/deepseek-r1:free",
        messages= history
    )

    reply = response.choices[0].message.content.strip()
    history.append({"role": "assistant", "content": reply})

    return reply, history
    

if __name__ == "__main__":

    # Get arguments from command line
    thy = sys.argv[1]
    lemma = sys.argv[2]
    error = sys.argv[3]
    line = sys.argv[4]
    history_json = sys.argv[5]

    # Open history from json file
    with open(history_json, "r") as f:
        chat_history = json.load(f)

    # No chat history means this is the first llm call for this lemma   
    if len(chat_history) == 0:

        chat_history.append({"role": "system", "content": "You are a theorem proving expert in Isabelle. Prove only the theorems that are given to you. You may use any other proven statement within the .thy file or its imports."})
        input = preamble + "\n" + thy + "\n" + lemma_proof + "\n" + lemma + "\n" + request 
    
    # Returning failed proof
    else:
        
        input = fail_return + "\n" + lemma + "\n" + line_error + "\n" + line + "\n" + error_message + "\n" + error + "\n" + error_request

    output, chat_history = query_llm(input, chat_history)
    with open(history_json, "w") as f:
        json.dump(chat_history, f, indent=2)

    print(json.dumps({
        "input": input,
        "output": output
    }))

    
  