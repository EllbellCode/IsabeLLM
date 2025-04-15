import os
import sys
from openai import OpenAI

preamble = "I am trying to complete a proof in Isabelle. Here is my theory file so far:"
lemma_proof = "I am trying to prove the following lemma:"
request = "Please prove this lemma. " \
          "Return only the raw code without any additional text, explanations, or formatting. " \
          "Do not include ``` or language tags. Just the pure code."

fail_return = "Your proof is incorrect. The current proof state is:"
line_error = "The line: "
error_message = "produced the following error message:"
error_request = "Please amend the proof to deal with this error." \
                "Return only the raw code without any additional text, explanations, or formatting. " \
                "Do not include ``` or language tags. Just the pure code."

api_key = os.getenv("OPENAI_API_KEY")

# Initialize client
client = OpenAI(
    base_url="https://openrouter.ai/api/v1",
    api_key= api_key
)

def query_llm(prompt: str) -> str:
    response = client.chat.completions.create(
        model="deepseek/deepseek-r1:free",
        messages=[{"role": "user", "content": prompt}]
    )
    return response.choices[0].message.content.strip()
    

if __name__ == "__main__":
    # Get arguments from command line
    thy = sys.argv[1]
    lemma = sys.argv[2]
    error = sys.argv[3]
    line = sys.argv[4]
    mode = int(sys.argv[5])

    if mode == 0:
        
        input = preamble + "\n" + thy + "\n" + lemma_proof + "\n" + lemma + "\n" + request 
    
    #Returning failed proof
    else:
        
        input = fail_return + "\n" + lemma + "\n" + line_error + "\n" + line + "\n" + error_message + "\n" + error + "\n" + error_request

    print("===INPUT===")
    print(input)   
    output = query_llm(input)
    print("===OUTPUT===")
    print(output)

  