# TODO

Ideas and potential improvements for the Aristotle MCP server.

## Feature Ideas

### Split check vs save for async proofs
Currently `check_prove_file` both checks status AND writes the file when complete. Consider:
- Add `save=False` parameter to check without saving
- Add separate `save_proof` tool for explicit file writing
- Gives users more control over when/where to save

### Prove single theorem from file
The `prove` tool handles code snippets but isn't file-aware. Could add:
- `prove_theorem(file_path, theorem_name)` to prove a specific theorem
- Would need to parse Lean file and extract the theorem with its context
- Useful when you only want to prove one thing without waiting for the whole file

### Async support for formalize
Currently `formalize` is sync-only while `prove` and `prove_file` support async mode.
- Add `wait: bool = True` parameter to `formalize`
- Add `check_formalize` tool for polling async formalization jobs
- Especially useful when `prove=True` since proving can take minutes
- Would make the API consistent across all tools

### Cancel queued jobs
Would be nice to cancel a proof that's queued if you realize you made a mistake.
- **Blocked**: aristotlelib API doesn't currently support cancellation
- Revisit if API adds this capability

## Documentation

### Clarify "check" vs "poll" terminology
The `check_proof` and `check_prove_file` tools are really polling operations for async jobs. Documentation should consistently use "poll" terminology to make this clearer:
- Tool descriptions should say "Poll for async proof status" not "Check status"
- README and docstrings should emphasize these are for polling async submissions
- Consider renaming tools to `poll_proof` / `poll_prove_file` in a future breaking change

## Installation / Configuration

### API key configuration for git-based installs
When users install MCP servers by pointing at a git repo (e.g., `uvx`, `npx`), how do they provide their API key?

Options to explore:
- Environment variable (current approach) - works but requires manual setup
- Config file in user's home directory (e.g., `~/.config/aristotle/config.json`)
- Interactive prompt on first run?
- MCP resource that returns setup instructions if not configured?

Need to document the recommended approach clearly.
