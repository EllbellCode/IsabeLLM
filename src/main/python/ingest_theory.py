import re
import sys
from send_to_llm import store_proof

# ==========================================
# REGEX PATTERNS
# ==========================================

LEMMA_START = re.compile(r'^\s*(lemma|theorem|corollary|proposition|subgoal)\s+([a-zA-Z0-9_]+)', re.MULTILINE)
LOCALE_START = re.compile(r'locale\s+([a-zA-Z0-9_]+).*?begin', re.DOTALL)
SECTION_END = re.compile(r'^\s*end\s*$', re.MULTILINE)

# Matches definitions and captures (Type, Name)
# e.g., "datatype 'a tree" -> group(2) = "tree"
DEF_PATTERN = re.compile(r'^\s*(datatype|fun|primrec|definition|abbreviation|record)\s+(?:[\w\'\(\)\.]+\s+)*([a-zA-Z0-9_]+)', re.MULTILINE)

PROOF_START_KEYWORDS = ["proof", "by", "apply"]

def get_def_blocks(thy_content):
    """
    Returns a dict: { "name": "full_code_string" }
    """
    definitions = {}
    
    # Heuristic split by top-level commands to isolate blocks
    command_iter = re.finditer(r'^\s*(datatype|fun|primrec|definition|abbreviation|record|lemma|theorem|proposition)', thy_content, re.MULTILINE)
    
    indices = [m.start() for m in command_iter]
    indices.append(len(thy_content))
    
    for i in range(len(indices) - 1):
        block = thy_content[indices[i]:indices[i+1]].strip()
        
        # Check if it is a definition
        match = DEF_PATTERN.match(block)
        if match:
            name = match.group(2)
            definitions[name] = block
            
    return definitions

def build_dependency_graph(definitions):
    """
    Returns a dict: { "func_name": ["dep1", "dep2"] }
    Scans each definition's body to see what OTHER definitions it mentions.
    """
    graph = {name: [] for name in definitions}
    
    for name, code in definitions.items():
        # Check every other definition to see if it is used here
        for potential_dep in definitions:
            if name == potential_dep:
                continue
            
            # Simple word-boundary check: does "tree" appear in "primrec height..."?
            if re.search(r'\b' + re.escape(potential_dep) + r'\b', code):
                graph[name].append(potential_dep)
                
    return graph

def get_transitive_deps(roots, graph):
    """
    Performs BFS to find ALL recursive dependencies for a list of root terms.
    Returns a set of all required definition names.
    """
    visited = set()
    queue = list(roots)
    
    while queue:
        current = queue.pop(0)
        if current in visited:
            continue
        visited.add(current)
        
        # Add children to queue
        children = graph.get(current, [])
        for child in children:
            if child not in visited:
                queue.append(child)
                
    return visited

def extract_proofs_recursive(thy_content):
    # 1. Catalog Definitions
    definitions = get_def_blocks(thy_content)
    
    # 2. Build Dependency Map (Who uses whom?)
    dep_graph = build_dependency_graph(definitions)
    
    tokens = re.split(LEMMA_START, thy_content)
    
    current_locale = "Global"
    if LOCALE_START.search(tokens[0]):
        current_locale = LOCALE_START.search(tokens[0]).group(1)

    for i in range(1, len(tokens), 3):
        lemma_type = tokens[i]
        lemma_name = tokens[i+1]
        raw_content = tokens[i+2]
        
        # --- A. Extract Proof Body ---
        proof_start_index = -1
        for keyword in PROOF_START_KEYWORDS:
            match = re.search(r'\b' + keyword + r'\b', raw_content)
            if match:
                if proof_start_index == -1 or match.start() < proof_start_index:
                    proof_start_index = match.start()

        if proof_start_index != -1:
            statement_part = raw_content[:proof_start_index].strip()
            proof_body = raw_content[proof_start_index:].strip()
            
            # Locale Exit Check
            save_locale = current_locale
            if re.search(r'\bqed\s+end\b', proof_body) or re.search(r'\bby\s+.*?\s+end\b', proof_body):
                 current_locale = "Global"
            
            # --- B. Recursive Context Resolution ---
            # 1. Find direct dependencies in the lemma statement
            direct_deps = []
            for name in definitions:
                if re.search(r'\b' + re.escape(name) + r'\b', statement_part):
                    direct_deps.append(name)
            
            # 2. Find ALL recursive dependencies
            all_deps = get_transitive_deps(direct_deps, dep_graph)
            
            # 3. Sort dependencies (Naive topological sort via string length or alphabetical)
            # ideally, 'datatype' should come before 'fun'. 
            # We can just iterate the original 'definitions' dict order as it's likely file-order.
            
            enriched_proof = ""
            if all_deps:
                enriched_proof += "(* Recursive Context *)\n"
                # Add them in order of appearance in the file (to ensure types define before use)
                for name, code in definitions.items():
                    if name in all_deps:
                        enriched_proof += code + "\n\n"
                enriched_proof += "(* Proof *)\n"
            
            enriched_proof += proof_body
            full_statement = f"Context: {save_locale}\n{lemma_type} {lemma_name}:\n{statement_part}"
            
            yield lemma_name, full_statement, enriched_proof

            # Locale Entry/Exit Checks
            new_locale_match = LOCALE_START.search(raw_content)
            if new_locale_match:
                current_locale = new_locale_match.group(1)
            if re.search(r'^\s*end\s*$', raw_content, re.MULTILINE):
                 if save_locale != "Global": current_locale = "Global"

def ingest_file(filename):
    with open(filename, 'r', encoding='utf-8') as f:
        content = f.read()

    print(f"Ingesting with RECURSIVE Context from {filename}...")
    
    count = 0
    for name, statement, proof in extract_proofs_recursive(content):
        print(f"Processing: {name}...")
        
        store_proof(filename, statement, proof, overwrite=False) 
        
        count += 1
    print(f"Finished. Processed {count} proofs.")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python ingest_theory.py <file.thy>")
        sys.exit(1)
    ingest_file(sys.argv[1])