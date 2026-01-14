# TODO

Ideas and potential improvements for the Aristotle MCP server.

## Completed

- ✅ **Split check vs save for async proofs** - Added `save` parameter (default `False`) to `check_prove_file`
- ✅ **Async support for formalize** - Added `wait` parameter and `check_formalize` tool
- ✅ **Clarify "check" vs "poll" terminology** - Updated all documentation to use "poll" consistently

## Feature Ideas

### Prove single theorem from file
The `prove` tool handles code snippets but isn't file-aware. Could add:
- `prove_theorem(file_path, theorem_name)` to prove a specific theorem
- Would need to parse Lean file and extract the theorem with its context
- Useful when you only want to prove one thing without waiting for the whole file

### Cancel queued jobs
Would be nice to cancel a proof that's queued if you realize you made a mistake.
- **Blocked**: aristotlelib API doesn't currently support cancellation
- Revisit if API adds this capability

### Rename polling tools
Consider renaming `check_*` tools to `poll_*` in a future breaking change:
- `check_proof` → `poll_proof`
- `check_prove_file` → `poll_prove_file`
- `check_formalize` → `poll_formalize`

This would make it clearer these are for polling async jobs, not validating proofs.

## Installation / Configuration

### API key configuration for git-based installs
When users install MCP servers by pointing at a git repo (e.g., `uvx`, `npx`), how do they provide their API key?

Options to explore:
- Environment variable (current approach) - works but requires manual setup
- Config file in user's home directory (e.g., `~/.config/aristotle/config.json`)
- Interactive prompt on first run?
- MCP resource that returns setup instructions if not configured?

Need to document the recommended approach clearly.
