import os
import sys
from openai import OpenAI
import json

# ENFORCEMENT: System prompt modified to demand zero-prose and strict code output
system_setup = {"role": "system", "content": 
                """
                You are a theorem proving expert in Isabelle. 
                Prove only the theorems that are given to you. 
                You may use any other proven statement within the .thy file or its imports.
                """}

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

aikey = os.getenv("aikey")
if not aikey:
    raise EnvironmentError("API key not found in environment variable 'aikey'.")

client = OpenAI(
    base_url="https://openrouter.ai/api/v1",
    api_key=aikey
)

def query_llm(prompt: str, history: list) -> tuple[str, list]:
    history.append({"role": "user", "content": prompt})
    
    # PARAMETER TUNING: Lower temperature for higher predictability
    response = client.chat.completions.create(
        model="deepseek/deepseek-r1-0528:free",
        messages=history,
        # temperature=0.2,
        # max_tokens=2048
    )

    reply = response.choices[0].message.content.strip()
    
    # CLEANUP: Redundant check to strip markdown if the LLM ignores instructions
    if "```" in reply:
        reply = reply.split("```")[-2].split("\n", 1)[-1].strip()
    
    if reply:
        history.append({"role": "assistant", "content": reply})
    else:
        history.pop()

    return reply, history

if __name__ == "__main__":
    # Get arguments from command line
    thy = sys.argv[1]
    lemma_all = sys.argv[2]
    error = sys.argv[3]
    line = sys.argv[4]
    history_json = sys.argv[5]

    with open(history_json, "r") as f:
        chat_history = json.load(f)

    if len(chat_history) == 0:
        # First call: Provide full theory context and the lemma to prove
        input_prompt = f"{preamble}{thy}{lemma_proof}{lemma_all}{request}" 
    else:
        # Subsequent call: Provide error feedback for correction
        input_prompt = f"{fail_return}{lemma_all}\n{line_error}{line}\n{error_message}{error}{error_request}"

    chat_history_ = [system_setup] + chat_history
    output, chat_history = query_llm(input_prompt, chat_history_)
    
    # Maintain only the last 10 turns to prevent context window bloat
    chat_history = chat_history[-10:] if len(chat_history) > 10 else chat_history
    
    # Save history without the system setup (it is prepended on next run)
    if chat_history and chat_history[0]["role"] == "system":
        chat_history.pop(0)
    
    with open(history_json, "w") as f:
        json.dump(chat_history, f, indent=2)

    print(json.dumps({
        "input": input_prompt,
        "output": output
    }))