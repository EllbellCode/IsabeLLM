"""
Used to test the OpenRouter API connection
"""

import os
from openai import OpenAI
from openai.types.chat import ChatCompletion
import pprint

aikey = os.getenv("aikey")
if not aikey:
    raise EnvironmentError("API key not found in environment variable 'aikey'.")

client = OpenAI(
    base_url="https://openrouter.ai/api/v1",
    api_key=aikey
)

def test_api():
    messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": "What is the capital of France?"}
    ]

    try:
        response: ChatCompletion = client.chat.completions.create(
            model="deepseek/deepseek-r1-0528:free",
            messages=messages
        )

        if hasattr(response, "choices") and response.choices:
            reply = response.choices[0].message.content.strip()
            print("✅ API call successful.\n")
            print("Response:\n" + reply)
        else:
            print("⚠️ API call returned no valid choices.")
            pprint.pprint(response.dict())

    except Exception as e:
        print("🚨 API call failed:")
        print(str(e))

if __name__ == "__main__":
    test_api()