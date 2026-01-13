# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Code Quality Rules

**NEVER ignore linting or type checking rules.** If a check fails, fix the code properly. Do not:
- Add `# noqa` comments
- Add `# type: ignore` comments
- Add ignore rules to pyproject.toml
- Disable any checks in configuration

If a rule seems wrong for a specific case, fix the code structure to satisfy the rule properly.

## Project Overview

This is an MCP (Model Context Protocol) server that wraps Harmonic's Aristotle theorem prover, enabling AI assistants to invoke automated theorem proving during Lean 4 development. The server exposes tools for proving theorems, filling in `sorry` statements, and formalizing natural language to Lean 4.

## Development Commands

```bash
# Install dependencies (use virtual environment)
python -m venv .venv
source .venv/bin/activate
pip install -e .

# Install with API support (requires aristotlelib)
pip install -e ".[api]"

# Run the MCP server
python -m aristotle_mcp

# Run in mock mode (no API key needed)
ARISTOTLE_MOCK=true python -m aristotle_mcp
```

## Environment Configuration

Copy `.env.example` to `.env` and set:
- `ARISTOTLE_API_KEY` - API key from https://aristotle.harmonic.fun/
- `ARISTOTLE_MOCK=true` - Enable mock mode for testing without API

## Architecture

```
src/aristotle_mcp/
├── __init__.py     # Package exports (main function)
├── __main__.py     # Entry point for `python -m aristotle_mcp`
├── server.py       # MCP server setup using FastMCP, tool registration
├── tools.py        # Tool implementations (prove, prove_file, formalize, check_proof)
└── mock.py         # Mock responses for testing without API
```

**Key flow:** `server.py` creates a FastMCP server and registers tools that delegate to `tools.py`. Each tool function checks `is_mock_mode()` to decide whether to use mock responses or call the real Aristotle API via `aristotlelib`.

## MCP Tools Provided

1. **`prove`** - Fill in `sorry` statements in Lean 4 code. Supports async mode with `wait=False` for long-running proofs.
2. **`check_proof`** - Poll status of async proof submissions.
3. **`prove_file`** - Prove all sorries in a Lean file with automatic import resolution.
4. **`formalize`** - Convert natural language math to Lean 4 code.

## MCP Resources

- `aristotle://status` - Returns connection status (mock_mode, api_key_configured, ready)

## Testing

Use `ARISTOTLE_MOCK=true` to test MCP protocol without API calls. Mock behavior in `mock.py`:
- Code containing `false_theorem` or `bad_lemma` returns counterexamples
- Code containing `timeout` or `hard` returns failed status
- Files with >5 sorries return partial success
