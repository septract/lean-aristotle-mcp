# Aristotle MCP Server

> **Note:** This project was 100% vibe-coded with [Claude Code](https://claude.ai/code).

An MCP (Model Context Protocol) server that wraps [Aristotle](https://aristotle.harmonic.fun/), Harmonic's automated theorem prover for Lean 4. This enables AI assistants to strategically invoke theorem proving during Lean development—filling in `sorry` statements, verifying lemmas, or formalizing natural language into Lean code.

## What is Aristotle?

[Aristotle](https://aristotle.harmonic.fun/) is a cloud-based theorem proving service by [Harmonic](https://harmonic.fun/) that can automatically fill in proofs in Lean 4. Given Lean code with `sorry` placeholders, Aristotle attempts to find valid proofs using advanced search techniques.

To use this MCP server, you'll need an API key from [aristotle.harmonic.fun](https://aristotle.harmonic.fun/).

## Tools Provided

| Tool | Description |
|------|-------------|
| `prove` | Fill in `sorry` statements in Lean code snippets |
| `prove_file` | Prove all sorries in a Lean file with automatic import resolution |
| `formalize` | Convert natural language math to Lean 4 code |
| `check_proof` | Poll async proof jobs for completion |
| `check_prove_file` | Poll async file proof jobs for completion |
| `check_formalize` | Poll async formalization jobs for completion |

## Installation

### Prerequisites

Install [uv](https://docs.astral.sh/uv/) (the fast Python package manager):

```bash
# macOS
brew install uv

# Or via shell script (macOS/Linux)
curl -LsSf https://astral.sh/uv/install.sh | sh
```

### Get Your API Key

1. Sign up at [aristotle.harmonic.fun](https://aristotle.harmonic.fun/)
2. Copy your API key
3. Add it to your shell configuration (`~/.zshrc` or `~/.bashrc`):

```bash
export ARISTOTLE_API_KEY="your-api-key-here"
```

Then restart your terminal or run `source ~/.zshrc`.

## Adding to Claude Code

### Option 1: Command Line (Recommended)

```bash
claude mcp add aristotle -e ARISTOTLE_API_KEY=$ARISTOTLE_API_KEY -- uvx --from git+https://github.com/septract/lean-aristotle-mcp aristotle-mcp
```

This registers the server with your API key from the environment. Use `--scope user` to make it available across all projects:

```bash
claude mcp add aristotle --scope user -e ARISTOTLE_API_KEY=$ARISTOTLE_API_KEY -- uvx --from git+https://github.com/septract/lean-aristotle-mcp aristotle-mcp
```

### Option 2: JSON Configuration

Add to your `~/.claude.json`:

```json
{
  "mcpServers": {
    "aristotle": {
      "type": "stdio",
      "command": "uvx",
      "args": ["--from", "git+https://github.com/septract/lean-aristotle-mcp", "aristotle-mcp"],
      "env": {
        "ARISTOTLE_API_KEY": "${ARISTOTLE_API_KEY}"
      }
    }
  }
}
```

The `${ARISTOTLE_API_KEY}` syntax expands to your shell environment variable.

### Verify Installation

```bash
claude mcp list              # Check server is registered
claude mcp get aristotle     # Test the connection
```

Or inside Claude Code, run `/mcp` to see connection status.

## Adding to Claude Desktop

Add to your `claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "aristotle": {
      "command": "uvx",
      "args": ["--from", "git+https://github.com/septract/lean-aristotle-mcp", "aristotle-mcp"],
      "env": {
        "ARISTOTLE_API_KEY": "your-api-key-here"
      }
    }
  }
}
```

**Note:** Claude Desktop doesn't expand environment variables, so you must include your actual API key.

## Mock Mode (Testing Without API Key)

To test the MCP server without making real API calls:

```bash
claude mcp add aristotle-mock -e ARISTOTLE_MOCK=true -- uvx --from git+https://github.com/septract/lean-aristotle-mcp aristotle-mcp
```

Or set in your configuration:

```json
{
  "env": {
    "ARISTOTLE_MOCK": "true"
  }
}
```

## Usage Notes

- **Proofs take time:** Aristotle proofs typically take 1-5 minutes. The tools support async mode (`wait=False`) for non-blocking operation.
- **Lean 4 only:** Aristotle works with Lean 4, not Lean 3 or earlier versions.
- **Mathlib support:** File-based proving automatically resolves Lake dependencies including Mathlib.

## Local Development

Clone the repository and install in editable mode:

```bash
git clone https://github.com/septract/lean-aristotle-mcp.git
cd lean-aristotle-mcp
make venv
source .venv/bin/activate
make install-dev  # Includes dev dependencies
```

Run the development server:

```bash
make run          # Uses real API
make run-mock     # Uses mock responses
```

The project uses a Makefile for common tasks. Run `make help` for all options.

```bash
make check      # Run lint + type-check
make test       # Run mock tests (no API key needed)
make test-api   # Run live API tests (requires ARISTOTLE_API_KEY)
make verify     # Full verification suite
```

## Troubleshooting

### "spawn uvx ENOENT" error

This means `uv` isn't in Claude's PATH. On macOS, GUI applications don't always inherit your shell PATH. Solutions:

1. **Restart Claude** after installing uv
2. **Use full path:** Replace `uvx` with the full path (e.g., `/opt/homebrew/bin/uvx`)
3. **Check installation:** Run `which uvx` in terminal to verify uv is installed

### "ARISTOTLE_API_KEY not set" error

Make sure you've:
1. Added `export ARISTOTLE_API_KEY="..."` to your shell config
2. Restarted your terminal
3. Included `-e ARISTOTLE_API_KEY=$ARISTOTLE_API_KEY` when adding the server

## License

MIT - see [LICENSE](LICENSE) for details.

## Links

- [Aristotle API](https://aristotle.harmonic.fun/) - Get your API key
- [Harmonic](https://harmonic.fun/) - Company behind Aristotle
- [aristotlelib on PyPI](https://pypi.org/project/aristotlelib/) - Python client library
- [Model Context Protocol](https://modelcontextprotocol.io/) - MCP specification
