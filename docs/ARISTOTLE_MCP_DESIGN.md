# Aristotle MCP Server Design Document

## Overview

This document describes an MCP (Model Context Protocol) server that wraps Harmonic's Aristotle theorem prover, enabling AI assistants like Claude to strategically invoke automated theorem proving during Lean 4 development.

## Motivation

When working on Lean 4 projects, there are frequent opportunities where automated theorem proving could accelerate development:

- Filling in `sorry` placeholders that the AI is uncertain how to prove
- Verifying that a proposed lemma is actually provable before building on it
- Finding counterexamples when a statement might be false
- Formalizing natural language mathematical specifications

Currently, users must manually invoke Aristotle. An MCP server would allow the AI assistant to call Aristotle strategically when it encounters proof obligations it cannot discharge.

## Architecture

```
┌─────────────────┐     MCP Protocol      ┌──────────────────┐
│  Claude Code    │◄────────────────────►│  aristotle-mcp   │
│  (MCP Client)   │     JSON-RPC/stdio    │  (MCP Server)    │
└─────────────────┘                       └────────┬─────────┘
                                                   │
                                                   │ Python SDK
                                                   ▼
                                          ┌──────────────────┐
                                          │  aristotlelib    │
                                          │  (Harmonic API)  │
                                          └────────┬─────────┘
                                                   │
                                                   │ HTTPS
                                                   ▼
                                          ┌──────────────────┐
                                          │  Aristotle API   │
                                          │  harmonic.fun    │
                                          └──────────────────┘
```

### Components

1. **aristotle-mcp**: Python MCP server using the `mcp` SDK
2. **aristotlelib**: Official Harmonic Python SDK (PyPI package)
3. **Aristotle API**: Harmonic's hosted theorem proving service

## MCP Tools

The tool design prioritizes clear AI decision-making. Rather than exposing SDK implementation details, tools are organized around distinct AI intents. The underlying Aristotle API returns proofs or counterexamples from the same endpoint—our tools interpret these results appropriately for each use case.

### 1. `prove`

Attempt to prove Lean code containing `sorry` statements. Returns the filled proof on success, or a counterexample if the statement is false.

**When to use:** The AI is stuck on a proof, wants to verify a lemma is true before building on it, or suspects a statement might be false.

**Parameters:**
| Name | Type | Required | Description |
|------|------|----------|-------------|
| `code` | string | Yes | Lean 4 code containing `sorry` statements |
| `context_files` | string[] | No | Paths to additional Lean files for imports |
| `hint` | string | No | Natural language hint to guide the prover |
| `wait` | boolean | No | If true (default), block until complete. If false, return immediately with project_id for polling. |

**Returns:**
```json
{
  "status": "proved | counterexample | failed | error | submitted | queued | in_progress",
  "code": "string (Lean code with sorries filled, if proved)",
  "counterexample": "string | null (if statement is false)",
  "project_id": "string | null (for async polling)",
  "message": "string (human-readable explanation)"
}
```

**Status values:**
- `proved`: All sorries filled successfully; `code` contains the solution
- `counterexample`: Statement is false; `counterexample` explains why
- `failed`: Could not prove (timeout, complexity); doesn't mean it's false
- `error`: Invalid input, API error, etc.
- `submitted`: Proof job submitted (when `wait=false`); use `check_proof` to poll
- `queued`: Proof is waiting to start
- `in_progress`: Proof is being computed

**Example - proving a theorem:**
```json
{
  "code": "theorem add_comm (a b : Nat) : a + b = b + a := by sorry",
  "hint": "Use induction on a"
}
```

**Example - checking if a lemma is true:**
```json
{
  "code": "theorem my_lemma : ∀ n : Nat, n < n + 1 := by sorry"
}
```

**Example - async submission:**
```json
{
  "code": "theorem hard_theorem : ... := by sorry",
  "wait": false
}
// Returns: {"status": "submitted", "project_id": "abc-123", "message": "..."}
```

### 2. `check_proof`

Check the status of a previously submitted proof job.

**When to use:** After calling `prove` with `wait=false`, poll this tool to check if the proof is complete.

**Parameters:**
| Name | Type | Required | Description |
|------|------|----------|-------------|
| `project_id` | string | Yes | The project ID returned from `prove(wait=false)` |

**Returns:**
```json
{
  "status": "queued | in_progress | proved | failed | error",
  "project_id": "string",
  "percent_complete": "number (0-100)",
  "code": "string | null (if proved)",
  "message": "string"
}
```

**Example:**
```json
{
  "project_id": "abc-123"
}
// Returns: {"status": "in_progress", "percent_complete": 45, "project_id": "abc-123", ...}
// Later:   {"status": "proved", "percent_complete": 100, "code": "theorem hard_theorem : ...", ...}
```

### 3. `prove_file`

Prove all `sorry` statements in a Lean file, with automatic import resolution from the project's lake dependencies.

**When to use:** The AI is working with an existing Lean file and wants to fill in all proof obligations at once.

**Parameters:**
| Name | Type | Required | Description |
|------|------|----------|-------------|
| `file_path` | string | Yes | Path to Lean file with `sorry` statements |
| `output_path` | string | No | Where to write solution (default: `{file}.solved.lean`) |
| `wait` | boolean | No | If true (default), block until complete. If false, return project_id for polling. |

**Returns:**
```json
{
  "status": "proved | partial | failed | error | submitted | queued | in_progress",
  "output_path": "string (path to solution file)",
  "sorries_filled": "number",
  "sorries_total": "number",
  "project_id": "string | null (for async polling)",
  "percent_complete": "number | null (0-100)",
  "message": "string"
}
```

**Status values:**
- `proved`: All sorries filled
- `partial`: Some sorries filled (see counts)
- `failed`: No sorries could be filled
- `error`: File not found, parse error, etc.
- `submitted`: Job submitted (when `wait=false`); use `check_prove_file` to poll
- `queued`: Waiting to start
- `in_progress`: Being computed

### 4. `check_prove_file`

Check the status of a previously submitted file proof job.

**When to use:** After calling `prove_file` with `wait=false`, poll this tool to check if the proof is complete.

**Parameters:**
| Name | Type | Required | Description |
|------|------|----------|-------------|
| `project_id` | string | Yes | The project ID returned from `prove_file(wait=false)` |
| `output_path` | string | No | Where to write solution when complete |

**Returns:**
```json
{
  "status": "queued | in_progress | proved | partial | failed | error",
  "project_id": "string",
  "percent_complete": "number (0-100)",
  "sorries_filled": "number (when complete)",
  "sorries_total": "number (when complete)",
  "output_path": "string (when complete)",
  "message": "string"
}
```

### 5. `formalize`

Convert a natural language mathematical statement into Lean 4 code.

**When to use:** The AI has a mathematical concept described in English and needs to express it formally, or wants to verify a natural language claim.

**Parameters:**
| Name | Type | Required | Description |
|------|------|----------|-------------|
| `description` | string | Yes | Natural language math statement or problem |
| `prove` | boolean | No | Also attempt to prove the formalized statement (default: false) |
| `context_file` | string | No | Path to a Lean file providing definitions/context for formalization |

**Returns:**
```json
{
  "status": "formalized | proved | failed | error",
  "lean_code": "string (formalized Lean 4 code)",
  "message": "string"
}
```

**Status values:**
- `formalized`: Successfully converted to Lean (when `prove=false`)
- `proved`: Formalized and proved (when `prove=true`)
- `failed`: Could not formalize or prove
- `error`: API error

**Example:**
```json
{
  "description": "The sum of two even numbers is even",
  "prove": true
}
```

## MCP Resources

### `aristotle://status`

Returns current API status and usage information.

```json
{
  "authenticated": boolean,
  "projects_today": number,
  "api_healthy": boolean
}
```

## Authentication

The server reads the API key from the environment:

```bash
export ARISTOTLE_API_KEY="your-api-key"
```

The key is obtained from [aristotle.harmonic.fun](https://aristotle.harmonic.fun/) after signing up.

## Configuration

### Claude Code MCP Configuration

Add to `~/.claude/settings.json` or project `.claude/settings.json`:

```json
{
  "mcpServers": {
    "aristotle": {
      "command": "python",
      "args": ["-m", "aristotle_mcp"],
      "env": {
        "ARISTOTLE_API_KEY": "${ARISTOTLE_API_KEY}"
      }
    }
  }
}
```

Or if installed as a standalone:

```json
{
  "mcpServers": {
    "aristotle": {
      "command": "aristotle-mcp",
      "env": {
        "ARISTOTLE_API_KEY": "${ARISTOTLE_API_KEY}"
      }
    }
  }
}
```

## Implementation Plan

### Phase 1: Core Structure (Mock Mode)
1. Set up Python project with `mcp` dependency
2. Implement MCP server skeleton with all 3 tools defined
3. Add mock mode (`ARISTOTLE_MOCK=true`) for testing without API
4. Implement mock responses that simulate real API behavior
5. Test MCP protocol compliance with Claude Code

### Phase 2: API Integration
6. Add `aristotlelib` dependency
7. Implement `prove` tool with real API calls
8. Implement `prove_file` tool
9. Implement `formalize` tool
10. Error handling for API failures, timeouts, rate limits

### Phase 3: Polish
11. Add `aristotle://status` resource
12. Comprehensive error messages with actionable guidance
13. Caching for repeated queries
14. Logging and diagnostics

## Project Structure

```
aristotle-mcp/
├── README.md
├── pyproject.toml
├── src/
│   └── aristotle_mcp/
│       ├── __init__.py
│       ├── __main__.py      # Entry point: python -m aristotle_mcp
│       ├── server.py        # MCP server setup and tool registration
│       ├── tools.py         # Tool implementations (prove, prove_file, formalize)
│       └── mock.py          # Mock responses for testing without API
└── tests/
    ├── test_tools.py
    └── test_server.py       # MCP protocol tests
```

## Dependencies

```toml
[project]
name = "aristotle-mcp"
version = "0.1.0"
requires-python = ">=3.10"
dependencies = [
    "mcp>=1.0.0",
]

[project.optional-dependencies]
api = ["aristotlelib>=0.6.0"]  # Required for real API calls

[project.scripts]
aristotle-mcp = "aristotle_mcp:main"
```

**Note:** In mock mode (`ARISTOTLE_MOCK=true`), `aristotlelib` is not required. This allows testing the MCP server structure without API credentials.

## Error Handling

### API Errors
- **Authentication failure**: Clear message about missing/invalid API key
- **Rate limiting**: Report wait time, suggest retry
- **Timeout**: Aristotle proofs can take time; report progress if possible

### Proof Failures
- **Unprovable**: Return clearly that proof was not found (not necessarily false)
- **Counterexample found**: Return the counterexample with explanation
- **Parse error**: Return Lean error message for malformed input

## Usage Scenarios

### Scenario 1: AI Encounters Difficult Proof

```
User: "Prove that this function terminates"

Claude: I've written the termination proof structure but this
arithmetic lemma is non-trivial. Let me ask Aristotle to fill it in.

[Calls prove with the sorry]
→ status: "proved", code: "..."

Claude: Aristotle found a proof using well-founded recursion on
the lexicographic order. Here's the completed proof: ...
```

### Scenario 2: Validating a Lemma Before Building on It

```
Claude: Before I build on this lemma, let me verify it's actually
true.

[Calls prove with "theorem my_lemma : ... := by sorry"]
→ status: "proved"

Claude: Aristotle confirmed this is provable. Proceeding with the
implementation that depends on it.
```

### Scenario 3: Finding Specification Bugs

```
User: "Why isn't my invariant preserved?"

Claude: Let me check if your invariant statement might be too strong.

[Calls prove with the invariant as a theorem]
→ status: "counterexample", counterexample: "n = 0, m = -1"

Claude: Aristotle found a counterexample: when n = 0 and m = -1,
the invariant fails because... You may want to add a precondition.
```

### Scenario 4: Formalizing Natural Language Math

```
User: "I want to prove that prime numbers greater than 2 are odd"

Claude: Let me formalize that statement in Lean first.

[Calls formalize with description, prove=true]
→ status: "proved", lean_code: "theorem prime_gt_two_odd..."

Claude: Here's the formalized theorem with proof: ...
```

## Security Considerations

- API key stored in environment, never logged
- No arbitrary code execution (Aristotle runs in Harmonic's sandbox)
- File paths validated before access
- Rate limiting to prevent accidental API abuse

## Future Extensions

- **Caching**: Cache proof results for identical queries
- **Batch proving**: Submit multiple theorems in parallel
- **Project awareness**: Automatically detect and use lake dependencies
- **Proof explanation**: Request human-readable proof explanations
- **Partial progress**: Stream partial results for long-running proofs

## References

- [Aristotle API](https://aristotle.harmonic.fun/)
- [aristotlelib on PyPI](https://pypi.org/project/aristotlelib/)
- [Aristotle Paper](https://arxiv.org/abs/2510.01346)
- [MCP Specification](https://modelcontextprotocol.io/specification)
- [MCP Python SDK](https://github.com/modelcontextprotocol/python-sdk)
