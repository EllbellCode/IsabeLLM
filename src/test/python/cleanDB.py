import os
import json
import re
import chromadb

# 1. Bring in your aggressive normalizer
def extract_core_statement(text):
    if not text: return ""
    clean = re.sub(r'^(?:lemma|theorem|corollary|proposition|subgoal)\s*(?:\(.*\))?\s*(?:\"[\w\']+\")?\s*:?', '', text.strip(), flags=re.IGNORECASE)
    clean = re.sub(r'^[\w\']+\s*:', '', clean)
    clean = clean.replace('"', '').replace("'", "")
    clean = "".join(clean.split())
    return clean

def clean_database():
    print("Connecting to ChromaDB...")
    chroma_client = chromadb.PersistentClient(path="./RAGdb")
    
    try:
        collection = chroma_client.get_collection(name="isabelle_proofs")
    except ValueError:
        print("Collection 'isabelle_proofs' not found. Exiting.")
        return

    # Fetch EVERYTHING currently in the database
    all_data = collection.get(include=["metadatas", "documents"])
    
    if not all_data['ids']:
        print("Database is already empty.")
        return

    seen_cores = set()
    ids_to_delete = []
    unique_mirror_data = []

    print(f"Scanning {len(all_data['ids'])} proofs for duplicates...")

    # 2. Iterate through and find the duplicates
    for i in range(len(all_data['ids'])):
        doc_id = all_data['ids'][i]
        metadata = all_data['metadatas'][i]
        proof_doc = all_data['documents'][i]
        
        lemma_text = metadata.get('lemma', '')
        core_stmt = extract_core_statement(lemma_text)

        if core_stmt in seen_cores:
            # We already have this exact logical lemma. Mark the ID for deletion.
            ids_to_delete.append(doc_id)
        else:
            # First time seeing this lemma. Keep it.
            seen_cores.add(core_stmt)
            unique_mirror_data.append({
                "lemma": lemma_text,
                "proof": proof_doc
            })

    # 3. Delete duplicates from ChromaDB
    if ids_to_delete:
        print(f"Found {len(ids_to_delete)} duplicate(s). Deleting from ChromaDB...")
        collection.delete(ids=ids_to_delete)
        print("ChromaDB cleaned successfully.")
    else:
        print("No duplicates found in ChromaDB.")

    # 4. Rebuild the JSON mirror to perfectly match the cleaned database
    mirror_file = "RAG_mirror.json"
    print(f"Rebuilding {mirror_file} with {len(unique_mirror_data)} unique entries...")
    with open(mirror_file, "w") as f:
        json.dump(unique_mirror_data, f, indent=4)
        
    print("Cleanup complete!")

if __name__ == "__main__":
    clean_database()