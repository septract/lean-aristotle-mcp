# AI User Stories for Aristotle MCP

This document describes the key workflows an AI assistant would use when invoking Aristotle during Lean 4 development.

## Story 1: Stuck on a Proof Step

**Scenario:** The AI is helping a user write Lean code and gets stuck on a specific proof step (e.g., arithmetic, termination argument).

**Flow:**
```
AI: "I can structure this proof but the nat arithmetic is tricky. Let me ask Aristotle."
→ prove(code="theorem foo : n + 0 = n := by sorry")
→ {"status": "proved", "code": "theorem foo : n + 0 = n := by simp"}
AI: "Aristotle filled it in using simp."
```

**Tool:** `prove(code, hint)` with `wait=True` (default)

**When to use:** The AI has written the proof structure but cannot discharge a specific obligation.

---

## Story 2: Lake Project with Multiple Files

**Scenario:** User has a Lean project with `lakefile.lean`, Mathlib dependencies, and custom definitions across multiple files. They want to prove theorems in a specific file.

**Flow (sync):**
```
AI: "Let me prove all the sorries in your theorem file."
→ prove_file(file_path="src/MyTheorem.lean")
→ Aristotle auto-imports all Lake dependencies and project files
→ {"status": "proved", "sorries_filled": 3, "sorries_total": 3, "output_path": "src/MyTheorem.solved.lean"}
```

**Flow (async for large files):**
```
AI: "This file has many theorems. I'll submit it and check back."
→ prove_file(file_path="src/BigFile.lean", wait=False)
→ {"status": "submitted", "project_id": "xyz-789", "sorries_total": 15}

AI: [polls later]
→ check_prove_file(project_id="xyz-789")
→ {"status": "in_progress", "percent_complete": 60}

AI: [polls again]
→ check_prove_file(project_id="xyz-789")
→ {"status": "proved", "percent_complete": 100, "sorries_filled": 15, "sorries_total": 15}
```

**Tools:** `prove_file(file_path)` with optional `wait=False`, `check_prove_file(project_id)` for polling

**When to use:** Working within an existing Lake project where imports and dependencies matter.

---

## Story 3: Long-Running Proof (Async)

**Scenario:** The AI submits a complex proof that may take several minutes. Rather than blocking, it submits asynchronously and polls for completion.

**Flow:**
```
AI: "This is a hard theorem. I'll submit it and check back."
→ prove(code="theorem hard : ... := by sorry", wait=False)
→ {"status": "submitted", "project_id": "abc-123"}

AI: [continues other work, then polls]
→ check_proof(project_id="abc-123")
→ {"status": "in_progress", "percent_complete": 45, "project_id": "abc-123"}
AI: "45% complete..."

AI: [waits, polls again]
→ check_proof(project_id="abc-123")
→ {"status": "proved", "percent_complete": 100, "code": "theorem hard : ... := by exact ..."}
```

**Tools:** `prove(wait=False)` to submit, `check_proof(project_id)` to poll

**When to use:** Complex proofs where blocking would waste time, or when the AI wants to do other work while waiting.

---

## Story 4: Verify a Lemma Before Building on It

**Scenario:** The AI is about to write code that depends on a lemma. Before proceeding, it wants to verify the lemma is actually true.

**Flow:**
```
AI: "Before I use this lemma, let me verify it's provable."
→ prove(code="theorem my_lemma : ∀ n : Nat, n < n + 1 := by sorry")
→ {"status": "proved"}
AI: "Confirmed. Proceeding with code that depends on my_lemma."
```

**Or if the lemma is false:**
```
→ prove(code="theorem bad_lemma : ∀ n : Nat, n < n := by sorry")
→ {"status": "counterexample", "counterexample": "n = 0 violates n < n"}
AI: "This lemma is false! Here's a counterexample: ..."
```

**Tool:** `prove(code)` — returns `counterexample` when statements are false

**When to use:** Sanity-checking assumptions before building on them, or debugging why a proof won't go through.

---

## Story 5: Formalize Natural Language Math

**Scenario:** User describes a mathematical statement in English. The AI needs to convert it to Lean 4 code.

**Flow (basic):**
```
User: "Prove that the sum of two even numbers is even"
AI: "Let me formalize and prove that statement."
→ formalize(description="The sum of two even numbers is even", prove=True)
→ {"status": "proved", "lean_code": "theorem even_add_even (a b : Nat) (ha : Even a) (hb : Even b) : Even (a + b) := by ..."}
AI: "Here's the formalized theorem with proof."
```

**Flow (with project context):**
```
User: "Prove that MyCustomType is commutative"
AI: "I'll use your definitions file as context."
→ formalize(
    description="MyCustomType operation is commutative",
    prove=True,
    context_file="src/Definitions.lean"
  )
→ {"status": "proved", "lean_code": "import Definitions\n\ntheorem mytype_comm ..."}
AI: "Formalized using your MyCustomType definition."
```

**Tool:** `formalize(description, prove=True, context_file=...)`

**When to use:** Converting informal math to Lean, or verifying natural language claims. Use `context_file` when your description references custom definitions from your project.

---

## Story 6: Standalone Files with Dependencies

**Scenario:** User has loose `.lean` files (not a full Lake project) that depend on each other.

**Flow:**
```
AI: "Your theorem uses definitions from other files. Let me include those."
→ prove(
    code="theorem uses_my_def : MyDef 5 := by sorry",
    context_files=["Definitions.lean", "Helpers.lean"]
  )
→ {"status": "proved", "code": "..."}
```

**Tool:** `prove(code, context_files=[...])` — manually specify context

**When to use:** Ad-hoc Lean files without Lake project structure, or when specific context is needed.

---

## API Timing Expectations

Based on testing, AI assistants should expect:

- **Queue time:** 30-60 seconds typical
- **Simple proofs:** 1-2 minutes total
- **Complex proofs:** 2-5+ minutes

The async workflow (Story 3) is recommended for anything non-trivial.
