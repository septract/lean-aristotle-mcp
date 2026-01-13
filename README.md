# Aristotle MCP Server

An MCP (Model Context Protocol) server that wraps Harmonic's Aristotle theorem prover, enabling AI assistants to strategically invoke automated theorem proving during Lean 4 development.

## Features

- **prove**: Fill in `sorry` statements in Lean code
- **check_proof**: Poll async proof jobs for completion
- **prove_file**: Prove all sorries in a Lean file
- **formalize**: Convert natural language math to Lean 4

## Installation

```bash
pip install aristotle-mcp
```

For API access (not mock mode):
```bash
pip install "aristotle-mcp[api]"
```

## Configuration

1. Copy `.env.example` to `.env`
2. Add your Aristotle API key (get one at https://aristotle.harmonic.fun/)

Or set the environment variable directly:
```bash
export ARISTOTLE_API_KEY=your-key-here
```

For testing without an API key:
```bash
export ARISTOTLE_MOCK=true
```

## Usage with Claude Code

Add to your Claude Code MCP configuration:

```bash
claude mcp add --transport stdio aristotle -- python -m aristotle_mcp
```

## Development

```bash
# Install with dev dependencies
pip install -e ".[dev]"

# Run type checking
mypy src/

# Run linting
ruff check src/

# Run tests
pytest
```

## License

MIT
