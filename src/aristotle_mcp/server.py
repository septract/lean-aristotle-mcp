"""MCP server for Aristotle theorem prover."""

from __future__ import annotations

import json
import sys

from mcp.server import FastMCP

from aristotle_mcp.models import ResultDict
from aristotle_mcp.tools import (
    check_formalize,
    check_proof,
    check_prove_file,
    formalize,
    has_api_key,
    is_mock_mode,
    prove,
    prove_file,
)

# Create the MCP server (no lifespan, so type parameter is None)
mcp: FastMCP[None] = FastMCP(
    name="aristotle-mcp",
    instructions=(
        "Aristotle theorem prover for Lean 4. Use 'prove' to fill in sorry statements, "
        "'prove_file' for file-based proving, and 'formalize' to convert natural language "
        "to Lean.\n\n"
        "IMPORTANT: Proofs can take several minutes to complete. When using wait=False for "
        "async operations, do NOT actively poll in a tight loop. Instead, inform the user "
        "that the proof is running and either: (1) continue with other work and check back "
        "later, or (2) ask the user when they'd like to check the status. Polling every few "
        "seconds wastes resources and provides no benefit since proofs typically take 1-5 "
        "minutes."
    ),
)


@mcp.tool(name="prove")
async def prove_tool(
    code: str,
    context_files: list[str] | None = None,
    hint: str | None = None,
    wait: bool = True,
) -> ResultDict:
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
    return result.to_dict()


@mcp.tool(name="check_proof")
async def check_proof_tool(project_id: str) -> ResultDict:
    """Poll for the status of a previously submitted proof.

    Use this tool to poll for results after calling prove with wait=False.

    IMPORTANT: Proofs typically take 1-5 minutes. Do not poll in a tight loop.
    Poll once, then continue with other work or ask the user before polling again.

    Args:
        project_id: The project ID returned from prove(wait=False)

    Returns:
        JSON with current status and progress. Fields:
        - status: "queued" | "in_progress" | "proved" | "failed" | "error"
        - percent_complete: 0-100 progress indicator
        - code: The proof (when status is "proved")
        - message: Human-readable status description
    """
    result = await check_proof(project_id=project_id)
    return result.to_dict()


@mcp.tool(name="prove_file")
async def prove_file_tool(
    file_path: str,
    output_path: str | None = None,
    wait: bool = True,
) -> ResultDict:
    """Prove all `sorry` statements in a Lean file.

    Automatically resolves imports from the project's lake dependencies.

    Use this tool when working with an existing Lean file and you want to
    fill in all proof obligations at once.

    Args:
        file_path: Path to Lean file with `sorry` statements
        output_path: Where to write the solution (default: {file}_aristotle.lean)
        wait: If True (default), block until complete. If False, submit
              and return immediately with project_id for polling.

    Returns:
        JSON with status, output_path, and message.
        If wait=False, returns status="submitted" with project_id for polling.
    """
    result = await prove_file(file_path=file_path, output_path=output_path, wait=wait)
    return result.to_dict()


@mcp.tool(name="check_prove_file")
async def check_prove_file_tool(
    project_id: str,
    output_path: str | None = None,
) -> ResultDict:
    """Poll for the status of a previously submitted file proof.

    Use this tool to poll for results after calling prove_file with wait=False.

    IMPORTANT: Proofs typically take 1-5 minutes. Do not poll in a tight loop.
    Poll once, then continue with other work or ask the user before polling again.

    Args:
        project_id: The project ID returned from prove_file(wait=False)
        output_path: Where to write the solution when complete (optional)

    Returns:
        JSON with current status and progress. Fields:
        - status: "queued" | "in_progress" | "proved" | "partial" | "failed" | "error"
        - percent_complete: 0-100 progress indicator
        - output_path: Path to solution file (when complete)
        - message: Human-readable status description
    """
    result = await check_prove_file(project_id=project_id, output_path=output_path)
    return result.to_dict()


@mcp.tool(name="formalize")
async def formalize_tool(
    description: str,
    prove: bool = False,
    context_file: str | None = None,
    wait: bool = True,
) -> ResultDict:
    """Convert a natural language mathematical statement into Lean 4 code.

    Use this tool when you have a mathematical concept described in English
    and need to express it formally, or want to verify a natural language
    mathematical claim.

    Args:
        description: Natural language math statement or problem
        prove: Also attempt to prove the formalized statement (default: false)
        context_file: Optional path to a Lean file providing definitions and
                      context for the formalization. Use this when your description
                      refers to custom types or definitions.
        wait: If True (default), block until complete. If False, submit
              and return immediately with project_id for polling.

    Returns:
        JSON with status (formalized/proved/failed/error), lean_code, and message.
        If wait=False, returns status="submitted" with project_id for polling.
    """
    result = await formalize(
        description=description, prove=prove, context_file=context_file, wait=wait
    )
    return result.to_dict()


@mcp.tool(name="check_formalize")
async def check_formalize_tool(project_id: str) -> ResultDict:
    """Poll for the status of a previously submitted formalization.

    Use this tool to poll for results after calling formalize with wait=False.

    IMPORTANT: Formalization typically takes 1-5 minutes. Do not poll in a tight loop.
    Poll once, then continue with other work or ask the user before polling again.

    Args:
        project_id: The project ID returned from formalize(wait=False)

    Returns:
        JSON with current status and progress. Fields:
        - status: "queued" | "in_progress" | "formalized" | "proved" | "failed" | "error"
        - percent_complete: 0-100 progress indicator
        - lean_code: The formalized Lean code (when complete)
        - message: Human-readable status description
    """
    result = await check_formalize(project_id=project_id)
    return result.to_dict()


@mcp.resource("aristotle://status")
async def get_status() -> str:
    """Get current status of the Aristotle connection."""
    mock_mode = is_mock_mode()
    api_key_configured = has_api_key()
    ready = mock_mode or api_key_configured

    if not ready:
        message = (
            "Not configured. Get your API key at https://aristotle.harmonic.fun/ "
            "and set ARISTOTLE_API_KEY, or set ARISTOTLE_MOCK=true for testing."
        )
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
