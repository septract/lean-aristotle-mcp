"""MCP server for Aristotle theorem prover."""

from __future__ import annotations

import json
import sys

from mcp.server import FastMCP

from aristotle_mcp.tools import (
    check_proof,
    formalize,
    has_api_key,
    is_mock_mode,
    prove,
    prove_file,
)

# Create the MCP server
mcp = FastMCP(
    name="aristotle-mcp",
    instructions=(
        "Aristotle theorem prover for Lean 4. Use 'prove' to fill in sorry statements, "
        "'prove_file' for file-based proving, and 'formalize' to convert natural language to Lean."
    ),
)


@mcp.tool(name="prove")
async def prove_tool(
    code: str,
    context_files: list[str] | None = None,
    hint: str | None = None,
    wait: bool = True,
) -> str:
    """Attempt to prove Lean 4 code containing `sorry` statements.

    Returns the filled proof on success, or a counterexample if the statement is false.

    Use this tool when:
    - You're stuck on a proof and need it filled in
    - You want to verify a lemma is true before building on it
    - You suspect a statement might be false and want to find a counterexample

    Args:
        code: Lean 4 code containing `sorry` statements to prove
        context_files: Optional paths to additional Lean files for imports
        hint: Optional natural language hint to guide the prover
        wait: If True (default), block until proof completes. If False, submit
              the proof and return immediately with a project_id for polling.

    Returns:
        JSON with status, code/counterexample, and message.
        If wait=False, returns status="submitted" with project_id to use with check_proof.
    """
    result = await prove(code=code, context_files=context_files, hint=hint, wait=wait)
    return json.dumps(result.to_dict(), indent=2)


@mcp.tool(name="check_proof")
async def check_proof_tool(project_id: str) -> str:
    """Check the status of a previously submitted proof.

    Use this tool to poll for results after calling prove with wait=False.

    Args:
        project_id: The project ID returned from prove(wait=False)

    Returns:
        JSON with current status. Possible statuses:
        - "queued": Waiting to start
        - "in_progress": Proof is being computed
        - "proved": Complete - code field contains the proof
        - "failed": Could not prove
        - "error": API error
    """
    result = await check_proof(project_id=project_id)
    return json.dumps(result.to_dict(), indent=2)


@mcp.tool(name="prove_file")
async def prove_file_tool(
    file_path: str,
    output_path: str | None = None,
) -> str:
    """Prove all `sorry` statements in a Lean file.

    Automatically resolves imports from the project's lake dependencies.

    Use this tool when working with an existing Lean file and you want to
    fill in all proof obligations at once.

    Args:
        file_path: Path to Lean file with `sorry` statements
        output_path: Where to write the solution (default: {file}.solved.lean)

    Returns:
        JSON with status (proved/partial/failed/error), output_path,
        sorries_filled, sorries_total, and message
    """
    result = await prove_file(file_path=file_path, output_path=output_path)
    return json.dumps(result.to_dict(), indent=2)


@mcp.tool(name="formalize")
async def formalize_tool(
    description: str,
    prove: bool = False,
) -> str:
    """Convert a natural language mathematical statement into Lean 4 code.

    Use this tool when you have a mathematical concept described in English
    and need to express it formally, or want to verify a natural language
    mathematical claim.

    Args:
        description: Natural language math statement or problem
        prove: Also attempt to prove the formalized statement (default: false)

    Returns:
        JSON with status (formalized/proved/failed/error), lean_code, and message
    """
    result = await formalize(description=description, prove=prove)
    return json.dumps(result.to_dict(), indent=2)


@mcp.resource("aristotle://status")
async def get_status() -> str:
    """Get current status of the Aristotle connection."""
    mock_mode = is_mock_mode()
    api_key_configured = has_api_key()
    ready = mock_mode or api_key_configured

    if not ready:
        message = "Set ARISTOTLE_API_KEY or ARISTOTLE_MOCK=true"
    elif mock_mode:
        message = "Running in mock mode (no API calls)"
    else:
        message = "Ready to call Aristotle API"

    status: dict[str, bool | str] = {
        "mock_mode": mock_mode,
        "api_key_configured": api_key_configured,
        "ready": ready,
        "message": message,
    }

    return json.dumps(status, indent=2)


def main() -> None:
    """Run the MCP server."""
    mode = "mock" if is_mock_mode() else "api"
    api_status = "configured" if has_api_key() else "not configured"

    # Log startup info to stderr (stdout is for MCP protocol)
    print(f"Aristotle MCP server starting (mode={mode}, api_key={api_status})", file=sys.stderr)

    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
