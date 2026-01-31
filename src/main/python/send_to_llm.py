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
# 2. STORAGE & RAG SYSTEM (With Filtering)
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

def extract_core_statement(text):
    """
    Aggressively normalizes a lemma statement for comparison.
    """
    if not text: return ""
    clean = re.sub(r'^(?:lemma|theorem|corollary|proposition|subgoal)\s*(?:\(.*\))?\s*(?:\"[\w\']+\")?\s*:?', '', text.strip(), flags=re.IGNORECASE)
    clean = re.sub(r'^[\w\']+\s*:', '', clean)
    clean = clean.replace('"', '').replace("'", "")
    clean = "".join(clean.split())
    return clean

def get_rag_context(current_lemma):
    if collection.count() == 0: return ""
    current_core = extract_core_statement(current_lemma)
    query_vec = embedder.encode([current_lemma]).tolist()
    results = collection.query(query_embeddings=query_vec, n_results=10)
    
    msg = "\n\n### Reference: Similar Successful Proofs ###\n"
    found = False
    count = 0

    if results['documents'] and results['documents'][0]:
        for doc, meta in zip(results['documents'][0], results['metadatas'][0]):
            stored_raw = meta.get('lemma', '')
            stored_core = extract_core_statement(stored_raw)

            if current_core == stored_core: continue
            if current_lemma.strip() in stored_raw or stored_raw in current_lemma.strip(): continue

            found = True
            count += 1
            msg += f"\n--- Example {count} ---\nLemma: {stored_raw}\nProof:\n{doc}\n"
            if count >= 3: break

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
        
        response = client.chat.completions.create(
            model = "tngtech/deepseek-r1t2-chimera:free",
            messages=messages,
            timeout= 12000
        )
        
        choice = response.choices[0]
        reply = choice.message.content

        if reply: reply = reply.strip()
        else: reply = ""

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
        
        # Capture error trace from Scala (defaults to empty)
        error_trace = sys.argv[6] if len(sys.argv) > 6 else ""
        
        rag_data = get_rag_context(lemma_all)
        
        try:
            with open(history_json, "r") as f: chat_history = json.load(f)
        except: chat_history = []

        # Format Trace Section
        trace_section = ""
        if error_trace:
            trace_section = f"\n\n### Execution Trace ###\nSince your last output, the system attempted the following automated fixes which resulted in the current state:\n{error_trace}\n"

        # ----------------------------------------------------
        # NEW: Critical Context for Nitpick / Counter-Examples
        # ----------------------------------------------------
        # Even if history is empty, if we have a counter-example, we must show it.
        critical_context = ""
        if error and ("Nitpick" in error or "Counter-example" in error or "genuine" in error):
             critical_context = f"\n\n### CRITICAL: COUNTER-EXAMPLE FOUND ###\nThe automated tool (Nitpick) found a counter-example to your lemma:\n{error}\n\nSince a counter-example exists, the lemma is likely false. Please MODIFY THE LEMMA STATEMENT (assumptions or conclusion) to exclude this case, or if you believe the lemma is correct, fix the proof structure."

        if len(chat_history) == 0:
            if critical_context:
                 # Inject Critical Context into first prompt
                 input_prompt = f"{preamble}\n{thy}\n{lemma_proof}\n{lemma_all}\n{critical_context}\n{request}"
            else:
                 # Standard first prompt
                 input_prompt = f"{preamble}\n{thy}\n{lemma_proof}\n{lemma_all}\n{request}"
        else:
            # Inject trace and critical context into retry prompt
            input_prompt = f"{fail_return}\n{lemma_all}\n{line_error}\n{line}\n{error_message}\n{error}{trace_section}{critical_context}\n{error_request}"

        output, hist = query_llm(input_prompt, chat_history, rag_context=rag_data)

        sys.stderr.write(f"\n[Python] Generated Proof:\n{output}\n")
        
        hist = hist[-10:] if len(hist) > 10 else hist
        
        with open(history_json, "w") as f: json.dump(hist, f, indent=2)
        
        print(json.dumps({"input": input_prompt, "output": output, "rag_active": bool(rag_data)}))