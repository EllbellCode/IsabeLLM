import os
import sys
import json
import hashlib
import re
import chromadb
from openai import OpenAI
from sentence_transformers import SentenceTransformer

# ==========================================
# 1. DEPENDENCY RESOLUTION LOGIC
# ==========================================

DEF_PATTERN = re.compile(r'^\s*(datatype|fun|primrec|definition|abbreviation|record)\s+(?:[\w\'\(\)\.]+\s+)*([a-zA-Z0-9_]+)', re.MULTILINE)

def get_def_blocks(thy_content):
    definitions = {}
    command_iter = re.finditer(r'^\s*(datatype|fun|primrec|definition|abbreviation|record|lemma|theorem|proposition)', thy_content, re.MULTILINE)
    indices = [m.start() for m in command_iter]
    indices.append(len(thy_content))
    
    for i in range(len(indices) - 1):
        block = thy_content[indices[i]:indices[i+1]].strip()
        match = DEF_PATTERN.match(block)
        if match:
            definitions[match.group(2)] = block
    return definitions

def build_dependency_graph(definitions):
    graph = {name: [] for name in definitions}
    for name, code in definitions.items():
        for potential_dep in definitions:
            if name == potential_dep: continue
            if re.search(r'\b' + re.escape(potential_dep) + r'\b', code):
                graph[name].append(potential_dep)
    return graph

def get_transitive_deps(roots, graph):
    visited = set()
    queue = list(roots)
    while queue:
        current = queue.pop(0)
        if current in visited: continue
        visited.add(current)
        for child in graph.get(current, []):
            if child not in visited: queue.append(child)
    return visited

def enrich_proof_with_context(thy_path, lemma_stmt, raw_proof):
    if not os.path.exists(thy_path):
        return raw_proof 

    with open(thy_path, 'r') as f:
        content = f.read()

    definitions = get_def_blocks(content)
    graph = build_dependency_graph(definitions)

    direct_deps = []
    for name in definitions:
        if re.search(r'\b' + re.escape(name) + r'\b', lemma_stmt):
            direct_deps.append(name)
            
    all_deps = get_transitive_deps(direct_deps, graph)

    if not all_deps:
        return raw_proof
        
    enriched = "(* Recursive Context *)\n"
    for name, code in definitions.items():
        if name in all_deps:
            enriched += code + "\n\n"
            
    enriched += "(* Proof *)\n" + raw_proof
    return enriched

# ==========================================
# 2. STORAGE & RAG SYSTEM
# ==========================================

chroma_client = chromadb.PersistentClient(path="./RAGdb")
collection = chroma_client.get_or_create_collection(name="isabelle_proofs")
JSON_MIRROR_FILE = "RAG_mirror.json"
embedder = SentenceTransformer('all-MiniLM-L6-v2')

def update_json_mirror(lemma_text, proof_code):
    if os.path.exists(JSON_MIRROR_FILE):
        try:
            with open(JSON_MIRROR_FILE, "r") as f: data = json.load(f)
        except: data = []
    else: data = []

    found = False
    for entry in data:
        if entry['lemma'] == lemma_text:
            entry['proof'] = proof_code
            found = True
            break
    if not found: data.append({"lemma": lemma_text, "proof": proof_code})

    with open(JSON_MIRROR_FILE, "w") as f: json.dump(data, f, indent=4)

def store_proof(thy_path, lemma_text, proof_code, overwrite=True):
    proof_id = hashlib.md5(lemma_text.encode()).hexdigest()

    if not overwrite:
        existing = collection.get(ids=[proof_id])
        if existing['ids']:
            sys.stderr.write(f"Skipping existing proof: {lemma_text[:30]}...\n")
            return

    final_proof = enrich_proof_with_context(thy_path, lemma_text, proof_code)
    
    embedding = embedder.encode(lemma_text).tolist()
    collection.upsert(
        documents=[final_proof],
        embeddings=[embedding],
        metadatas=[{"lemma": lemma_text}],
        ids=[proof_id]
    )

    update_json_mirror(lemma_text, final_proof)
    sys.stderr.write(f"Saved enriched proof for: {lemma_text[:30]}...\n")

def get_rag_context(current_lemma):
    if collection.count() == 0: return ""
    query_vec = embedder.encode([current_lemma]).tolist()
    results = collection.query(query_embeddings=query_vec, n_results=3)
    
    msg = "\n\n### Reference: Similar Successful Proofs ###\n"
    found = False
    if results['documents'] and results['documents'][0]:
        for i, (doc, meta) in enumerate(zip(results['documents'][0], results['metadatas'][0])):
            found = True
            msg += f"\n--- Example {i+1} ---\nLemma: {meta.get('lemma','')}\nProof:\n{doc}\n"
    return msg if found else ""

# ==========================================
# 3. LLM CLIENT
# ==========================================

def get_openai_client():
    aikey = os.getenv("aikey")
    if not aikey: 
        sys.stderr.write("Error: API Key missing in environment variable 'aikey'.\n")
        sys.exit(1)
    
    return OpenAI(base_url="https://openrouter.ai/api/v1", api_key=aikey)

base_system_content = """
You are a theorem proving expert in Isabelle. 
Prove only the theorems that are given to you. 
You may use any other proven statement within the .thy file or its imports.
"""

preamble = "I am trying to complete a proof in Isabelle. Here is my theory file so far:"
lemma_proof = "I am trying to prove the following lemma:"
request = "Please prove this lemma. Return only the raw code without any additional text, explanations, formatting, or commentary. Do not include ``` or language tags. Just the pure code."
fail_return = "Your proof is incorrect. The current proof state is:"
line_error = "The line: "
error_message = "produced the following error message:"
error_request = "Please amend the proof to deal with this error. Return only the raw code without any additional text, explanations, formatting, or commentary. Do not include ``` or language tags. Just the pure code."

def query_llm(prompt, history, rag_context=""):
    try:
        client = get_openai_client()
        messages = [{"role":"system", "content":base_system_content + rag_context}] + history + [{"role":"user", "content":prompt}]
        
        # Using the requested model with explicit timeout
        response = client.chat.completions.create(
            model = "tngtech/deepseek-r1t2-chimera:free",
            # model="deepseek/deepseek-r1-0528:free", 
            messages=messages,
            timeout= 12000
        )
        
        choice = response.choices[0]
        message = choice.message
        
        reply = message.content

        if reply:
            reply = reply.strip()
           
        else:
            # If standard content is empty, we return empty string.
            reply = ""
            sys.stderr.write(f"\n[Error] Standard 'content' field was empty\n")
            # sys.stderr.write(f"Raw Dump: {response.model_dump()}\n")

        history.append({"role":"user", "content":prompt})
        history.append({"role":"assistant", "content":reply})
        return reply, history
    except Exception as e:
        sys.stderr.write(f"LLM Fail: {e}\n")
        return "", history

# ==========================================
# 4. ENTRY POINT
# ==========================================

if __name__ == "__main__":
    
    mode = sys.argv[1] if len(sys.argv) > 1 else ""

    if mode == "store":
        if len(sys.argv) < 5:
            sys.stderr.write("Usage: python send_to_llm.py store <thy_path> <lemma> <proof>\n")
            sys.exit(1)
        
        thy_path = sys.argv[2]
        lemma = sys.argv[3]
        proof = sys.argv[4]
        store_proof(thy_path, lemma, proof, overwrite=True)
        
    else:
        thy = sys.argv[1]
        lemma_all = sys.argv[2]
        error = sys.argv[3]
        line = sys.argv[4]
        history_json = sys.argv[5]
        
        rag_data = get_rag_context(lemma_all)
        
        try:
            with open(history_json, "r") as f: chat_history = json.load(f)
        except: chat_history = []

        if len(chat_history) == 0:
            input_prompt = f"{preamble}\n{thy}\n{lemma_proof}\n{lemma_all}\n{request}"
        else:
            input_prompt = f"{fail_return}\n{lemma_all}\n{line_error}\n{line}\n{error_message}\n{error}\n{error_request}"

        output, hist = query_llm(input_prompt, chat_history, rag_context=rag_data)

        sys.stderr.write(f"\n[Python] Generated Proof:\n{output}\n")
        
        hist = hist[-10:] if len(hist) > 10 else hist
        
        with open(history_json, "w") as f: json.dump(hist, f, indent=2)
        
        print(json.dumps({"input": input_prompt, "output": output, "rag_active": bool(rag_data)}))