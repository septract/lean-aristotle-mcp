"""Tool implementations for the Aristotle MCP server."""

from __future__ import annotations

import logging
import os
import re
import tempfile
import threading
import time

from dotenv import load_dotenv

from aristotle_mcp.mock import (
    mock_check_proof,
    mock_check_prove_file,
    mock_formalize,
    mock_prove,
    mock_prove_file,
)
from aristotle_mcp.models import (
    FormalizeResult,
    ProveFileResult,
    ProveResult,
    ResultDict,
    ResultValue,
)

# Configure module logger
_logger = logging.getLogger(__name__)

# Re-export types for backwards compatibility
__all__ = [
    "ResultDict",
    "ResultValue",
    "ProveResult",
    "ProveFileResult",
    "FormalizeResult",
    "is_mock_mode",
    "has_api_key",
    "prove",
    "check_proof",
    "prove_file",
    "check_prove_file",
    "formalize",
]

# Regex for counting sorry statements (word boundary to avoid matching "sorryExample")
_SORRY_PATTERN = re.compile(r"\bsorry\b")

# Track whether .env has been loaded
_dotenv_loaded = False

# Thread lock for accessing shared state
_metadata_lock = threading.Lock()

# Metadata store for async proof jobs (persists across polls within server lifetime)
# Maps project_id -> metadata dict with timestamp for cleanup
# Access must be protected by _metadata_lock
_async_job_metadata: dict[str, dict[str, str | int | float]] = {}

# Cleanup jobs older than 1 hour
_METADATA_TTL_SECONDS = 3600

# Input size limits (defense-in-depth)
_MAX_CODE_SIZE = 1_000_000  # 1MB for code input
_MAX_DESCRIPTION_SIZE = 100_000  # 100KB for natural language descriptions
_MAX_FILE_SIZE = 10_000_000  # 10MB for file inputs

# Helpful error message for missing API key
_API_KEY_ERROR = (
    "ARISTOTLE_API_KEY environment variable not set. "
    "Get your API key at https://aristotle.harmonic.fun/ and set it with: "
    "export ARISTOTLE_API_KEY=your-key-here. "
    "For testing without an API key, set ARISTOTLE_MOCK=true."
)


def _count_sorries(text: str) -> int:
    """Count sorry statements in text using word boundary matching."""
    matches: list[str] = _SORRY_PATTERN.findall(text)
    return len(matches)


def _find_unique_path(path: str, max_attempts: int = 1000) -> str:
    """Find a unique path by adding a number suffix if the file exists.

    Uses atomic file creation to avoid TOCTOU race conditions.

    Example: foo_aristotle.lean -> foo_aristotle.1.lean -> foo_aristotle.2.lean

    Args:
        path: The base path to check
        max_attempts: Maximum number of suffixes to try before raising

    Returns:
        A path that was atomically created (empty file)

    Raises:
        RuntimeError: If no unique path found within max_attempts
    """
    # Try the original path first, then numbered variants
    candidates = [path] + [
        f"{os.path.splitext(path)[0]}.{i}{os.path.splitext(path)[1]}"
        for i in range(1, max_attempts + 1)
    ]

    for candidate in candidates:
        try:
            # O_CREAT | O_EXCL atomically creates file only if it doesn't exist
            fd = os.open(candidate, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o644)
            os.close(fd)
            return candidate
        except FileExistsError:
            continue

    raise RuntimeError(f"Could not find unique path after {max_attempts} attempts: {path}")


def _ensure_dotenv() -> None:
    """Load .env file if not already loaded."""
    global _dotenv_loaded
    if not _dotenv_loaded:
        load_dotenv()
        _dotenv_loaded = True


def _cleanup_stale_metadata() -> None:
    """Remove metadata entries older than TTL to prevent memory leaks.

    Thread-safe: acquires _metadata_lock.
    """
    now = time.time()
    with _metadata_lock:
        stale_ids = [
            pid for pid, meta in _async_job_metadata.items()
            if now - float(meta.get("timestamp", 0)) > _METADATA_TTL_SECONDS
        ]
        for pid in stale_ids:
            _async_job_metadata.pop(pid, None)


def _canonicalize_path(path: str) -> str:
    """Canonicalize a file path to prevent path traversal issues.

    Resolves symlinks, removes . and .. components, and returns absolute path.

    Args:
        path: The path to canonicalize

    Returns:
        Canonicalized absolute path
    """
    return os.path.realpath(os.path.abspath(path))


def _sanitize_api_error(error: Exception) -> str:
    """Sanitize an API error for safe return to clients.

    Logs the full error for debugging but returns a generic message
    to avoid leaking internal details.

    Args:
        error: The exception to sanitize

    Returns:
        A safe error message for the client
    """
    # Log full error for debugging
    _logger.exception("API error occurred")

    error_str = str(error).lower()

    # Return specific messages for known error types
    if "timeout" in error_str or "timed out" in error_str:
        return "Request timed out. Please try again."
    if "connection" in error_str or "network" in error_str:
        return "Connection error. Please check your network and try again."
    if "unauthorized" in error_str or "authentication" in error_str:
        return "Authentication failed. Please check your API key."
    if "rate limit" in error_str or "too many" in error_str:
        return "Rate limit exceeded. Please wait before retrying."
    if "not found" in error_str:
        return "Resource not found."
    if "counterexample" in error_str:
        # This is actually useful information, pass it through
        return str(error)

    # Generic fallback
    return "An error occurred while processing your request."


def _map_api_status(status_str: str, percent_complete: int | None) -> tuple[str, str]:
    """Map aristotlelib API status to our status and message.

    Args:
        status_str: Status string from the API (e.g., "COMPLETE", "QUEUED")
        percent_complete: Percent complete from the API

    Returns:
        Tuple of (status, message) for our result types
    """
    pct = percent_complete or 0

    if status_str == "COMPLETE":
        return "complete", "Proof completed"
    elif status_str in ("QUEUED", "NOT_STARTED"):
        return "queued", "Proof is queued, waiting to start"
    elif status_str == "IN_PROGRESS":
        return "in_progress", f"Proof is being computed ({pct}% complete)"
    elif status_str == "PENDING_RETRY":
        return "in_progress", "Proof is pending retry"
    elif status_str == "FAILED":
        return "failed", "Proof failed"
    else:
        return "in_progress", f"Status: {status_str}"


def _analyze_solution_file(
    solution_path: str,
    sorries_total: int,
    project_id: str | None = None,
) -> ProveFileResult:
    """Analyze a completed solution file and return the appropriate result.

    Args:
        solution_path: Path to the solution file
        sorries_total: Original number of sorries in the input
        project_id: Optional project ID to include in result

    Returns:
        ProveFileResult with status based on remaining sorries
    """
    absolute_path = os.path.abspath(solution_path)

    if not os.path.exists(absolute_path):
        return ProveFileResult(
            status="failed",
            project_id=project_id,
            sorries_total=sorries_total,
            percent_complete=100,
            message="Completed but solution file not found",
        )

    with open(absolute_path) as f:
        solved = f.read()

    remaining = _count_sorries(solved)
    filled = max(0, sorries_total - remaining)

    if remaining == 0:
        status = "proved"
    elif filled > 0:
        status = "partial"
    else:
        status = "failed"

    message = f"Filled {filled} of {sorries_total} sorry statements"
    if remaining > 0:
        message += f", {remaining} remaining"

    return ProveFileResult(
        status=status,
        output_path=absolute_path,
        sorries_filled=filled,
        sorries_total=sorries_total,
        project_id=project_id,
        percent_complete=100,
        message=message,
    )


def is_mock_mode() -> bool:
    """Check if we're running in mock mode."""
    _ensure_dotenv()
    return os.environ.get("ARISTOTLE_MOCK", "").lower() in ("true", "1", "yes")


def has_api_key() -> bool:
    """Check if an API key is configured."""
    _ensure_dotenv()
    return bool(os.environ.get("ARISTOTLE_API_KEY"))


async def prove(
    code: str,
    context_files: list[str] | None = None,
    hint: str | None = None,
    wait: bool = True,
) -> ProveResult:
    """Attempt to prove Lean code containing sorry statements.

    Args:
        code: Lean 4 code containing `sorry` statements
        context_files: Optional paths to additional Lean files for imports
        hint: Optional natural language hint to guide the prover
        wait: If True, block until proof completes. If False, return immediately
              with a project_id that can be polled with check_proof.

    Returns:
        ProveResult with status and either filled code or counterexample.
        If wait=False, returns status="submitted" with project_id for polling.
    """
    # Validate input size
    if len(code) > _MAX_CODE_SIZE:
        return ProveResult(
            status="error",
            message=f"Code exceeds maximum size of {_MAX_CODE_SIZE} bytes.",
        )

    if is_mock_mode():
        return mock_prove(code, context_files, hint, wait=wait)

    # Real API implementation
    if not has_api_key():
        return ProveResult(status="error", message=_API_KEY_ERROR)

    # Validate and canonicalize context files before making API calls
    canonicalized_context: list[str] | None = None
    if context_files:
        canonicalized_context = []
        for ctx_file in context_files:
            canonical = _canonicalize_path(ctx_file)
            if not os.path.exists(canonical):
                return ProveResult(
                    status="error",
                    message=f"Context file not found: {ctx_file}",
                )
            canonicalized_context.append(canonical)

    try:
        from aristotlelib import Project

        # Create project (async)
        project = await Project.create()

        # Add context files if provided (async)
        if canonicalized_context:
            await project.add_context(canonicalized_context)

        # If hint is provided, add it as a comment
        code_with_hint = code
        if hint:
            code_with_hint = f"-- Hint: {hint}\n{code}"

        # Solve with the provided code (async)
        await project.solve(input_content=code_with_hint)

        project_id = str(project.project_id)

        # If not waiting, return immediately with project_id
        if not wait:
            return ProveResult(
                status="submitted",
                project_id=project_id,
                message="Proof submitted. Use check_proof to poll for results.",
            )

        # Wait for completion with a temp output file
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            output_path = f.name

        try:
            solution_path = await project.wait_for_completion(output_file_path=output_path)

            if solution_path and os.path.exists(solution_path):
                with open(solution_path) as f:
                    solved_code = f.read()
                return ProveResult(
                    status="proved",
                    code=solved_code,
                    project_id=project_id,
                    message="Successfully proved",
                )
            else:
                # Check project status for more info
                await project.refresh()
                return ProveResult(
                    status="failed",
                    project_id=project_id,
                    message=f"Project status: {project.status}",
                )
        finally:
            # Clean up temp file
            if os.path.exists(output_path):
                os.unlink(output_path)

    except Exception as e:
        error_msg = str(e)
        # Try to detect counterexamples in error messages
        if "counterexample" in error_msg.lower():
            return ProveResult(
                status="counterexample",
                counterexample=error_msg,
                message="Statement appears to be false",
            )
        return ProveResult(
            status="error",
            message=_sanitize_api_error(e),
        )


async def check_proof(project_id: str) -> ProveResult:
    """Check the status of a previously submitted proof.

    Args:
        project_id: The project ID returned from prove(wait=False)

    Returns:
        ProveResult with current status. If complete, includes the proof code.
    """
    if is_mock_mode():
        return mock_check_proof(project_id)

    if not has_api_key():
        return ProveResult(status="error", message=_API_KEY_ERROR)

    try:
        from aristotlelib import Project

        # Load existing project
        project = await Project.from_id(project_id)
        await project.refresh()

        # Get status name from enum (e.g., ProjectStatus.QUEUED -> "QUEUED")
        status_str = (
            project.status.name if hasattr(project.status, "name") else str(project.status).upper()
        )
        pct = project.percent_complete

        # Map API status to our status
        our_status, message = _map_api_status(status_str, pct)

        if our_status == "complete":
            # Get the solution
            with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
                output_path = f.name

            try:
                solution_path = await project.get_solution(output_path=output_path)
                if solution_path and os.path.exists(solution_path):
                    with open(solution_path) as f:
                        solved_code = f.read()
                    return ProveResult(
                        status="proved",
                        code=solved_code,
                        project_id=project_id,
                        percent_complete=100,
                        message="Proof completed successfully",
                    )
            finally:
                if os.path.exists(output_path):
                    os.unlink(output_path)

            return ProveResult(
                status="failed",
                project_id=project_id,
                percent_complete=pct,
                message="Completed but no solution available",
            )

        return ProveResult(
            status=our_status,
            project_id=project_id,
            percent_complete=pct if our_status != "queued" else 0,
            message=message,
        )

    except Exception as e:
        return ProveResult(
            status="error",
            project_id=project_id,
            message=_sanitize_api_error(e),
        )


async def prove_file(
    file_path: str,
    output_path: str | None = None,
    wait: bool = True,
) -> ProveFileResult:
    """Prove all sorry statements in a Lean file.

    Args:
        file_path: Path to Lean file with sorry statements
        output_path: Where to write solution (default: {file}_aristotle.lean)
        wait: If True (default), block until complete. If False, return immediately
              with a project_id that can be polled with check_prove_file.

    Returns:
        ProveFileResult with status and counts.
        If wait=False, returns status="submitted" with project_id for polling.
    """
    # Canonicalize path to prevent traversal issues
    canonical_path = _canonicalize_path(file_path)

    if not os.path.exists(canonical_path):
        return ProveFileResult(
            status="error",
            message=f"File not found: {file_path}",
        )

    # Check file size before reading
    file_size = os.path.getsize(canonical_path)
    if file_size > _MAX_FILE_SIZE:
        return ProveFileResult(
            status="error",
            message=f"File exceeds maximum size of {_MAX_FILE_SIZE} bytes.",
        )

    # Determine the actual output path (matches aristotlelib's default naming)
    actual_output_path: str
    if output_path is None:
        base, ext = os.path.splitext(canonical_path)
        actual_output_path = f"{base}_aristotle{ext}"
    else:
        actual_output_path = _canonicalize_path(output_path)

    # Atomically check if output would overwrite existing file
    try:
        fd = os.open(actual_output_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o644)
        os.close(fd)
        # File created successfully, remove it so API can create it
        os.unlink(actual_output_path)
    except FileExistsError:
        return ProveFileResult(
            status="error",
            message=f"Output file already exists: {actual_output_path}",
        )

    # Count sorries in original file
    with open(canonical_path) as f:
        original = f.read()
    original_sorries = _count_sorries(original)

    if is_mock_mode():
        return mock_prove_file(file_path, output_path, wait=wait)

    # Real API implementation
    if not has_api_key():
        return ProveFileResult(status="error", message=_API_KEY_ERROR)

    try:
        from aristotlelib import Project, ProjectStatus

        # Use prove_from_file for both sync and async modes
        # This ensures auto_add_imports is used to handle local dependencies
        result = await Project.prove_from_file(
            input_file_path=canonical_path,
            output_file_path=actual_output_path,
            auto_add_imports=True,
            wait_for_completion=wait,
        )

        # For async mode, we need to find the project_id for polling
        if not wait:
            # NOTE: This is a potential race condition if multiple proofs are submitted
            # simultaneously. The aristotlelib API doesn't return project_id from
            # prove_from_file, so we have to find it by listing recent projects.
            # This should be fixed upstream in aristotlelib.
            projects, _ = await Project.list_projects(
                limit=5,
                status=[ProjectStatus.QUEUED, ProjectStatus.IN_PROGRESS, ProjectStatus.NOT_STARTED],
            )

            if not projects:
                return ProveFileResult(
                    status="error",
                    message="Could not find submitted project",
                )

            # Take the most recent project (first in list)
            project = projects[0]
            project_id = str(project.project_id)

            # Cleanup stale metadata before adding new entry
            _cleanup_stale_metadata()

            # Store metadata for retrieval when polling (thread-safe)
            with _metadata_lock:
                _async_job_metadata[project_id] = {
                    "file_path": canonical_path,
                    "output_path": actual_output_path,
                    "sorries_total": original_sorries,
                    "timestamp": time.time(),
                }

            return ProveFileResult(
                status="submitted",
                output_path=actual_output_path,
                sorries_total=original_sorries,
                project_id=project_id,
                message="Proof submitted. Use check_prove_file to poll for results.",
            )

        # Sync mode completed - analyze the result
        return _analyze_solution_file(result, original_sorries)

    except Exception as e:
        return ProveFileResult(
            status="error",
            message=_sanitize_api_error(e),
        )


async def check_prove_file(project_id: str, output_path: str | None = None) -> ProveFileResult:
    """Check the status of a previously submitted file proof.

    Args:
        project_id: The project ID returned from prove_file(wait=False)
        output_path: Where to write solution when complete (optional)

    Returns:
        ProveFileResult with current status. If complete, includes output_path and counts.
    """
    if is_mock_mode():
        return mock_check_prove_file(project_id)

    if not has_api_key():
        return ProveFileResult(status="error", message=_API_KEY_ERROR)

    # Retrieve stored metadata if available (thread-safe)
    with _metadata_lock:
        metadata = _async_job_metadata.get(project_id, {}).copy()
    stored_output_path = metadata.get("output_path")
    stored_sorries_total = metadata.get("sorries_total", 0)

    # Use stored output path if none provided
    if output_path is None and isinstance(stored_output_path, str):
        output_path = stored_output_path

    try:
        from aristotlelib import Project

        # Load existing project
        project = await Project.from_id(project_id)
        await project.refresh()

        # Get status and progress
        status_str = (
            project.status.name if hasattr(project.status, "name") else str(project.status).upper()
        )
        pct = project.percent_complete

        # Map API status to our status
        our_status, message = _map_api_status(status_str, pct)

        if our_status == "complete":
            # Find a unique path to avoid overwriting existing files
            safe_output_path = _find_unique_path(output_path) if output_path else None

            # Get the solution
            solution_path = await project.get_solution(output_path=safe_output_path)

            # Clean up metadata now that job is complete (thread-safe)
            with _metadata_lock:
                _async_job_metadata.pop(project_id, None)

            sorries_total = int(stored_sorries_total) if stored_sorries_total else 0
            return _analyze_solution_file(str(solution_path), sorries_total, project_id)

        elif our_status == "failed":
            # Clean up metadata for failed jobs (thread-safe)
            with _metadata_lock:
                _async_job_metadata.pop(project_id, None)

        return ProveFileResult(
            status=our_status,
            project_id=project_id,
            percent_complete=pct if our_status != "queued" else 0,
            message=message,
        )

    except Exception as e:
        return ProveFileResult(
            status="error",
            project_id=project_id,
            message=_sanitize_api_error(e),
        )


async def formalize(
    description: str,
    prove: bool = False,
    context_file: str | None = None,
) -> FormalizeResult:
    """Convert natural language math to Lean 4 code.

    Args:
        description: Natural language math statement or problem
        prove: Whether to also prove the formalized statement
        context_file: Optional path to a Lean file providing definitions and context
                      for the formalization

    Returns:
        FormalizeResult with status and Lean code
    """
    # Validate input size
    if len(description) > _MAX_DESCRIPTION_SIZE:
        return FormalizeResult(
            status="error",
            message=f"Description exceeds maximum size of {_MAX_DESCRIPTION_SIZE} bytes.",
        )

    if is_mock_mode():
        return mock_formalize(description, prove, context_file)

    # Real API implementation
    if not has_api_key():
        return FormalizeResult(status="error", message=_API_KEY_ERROR)

    # Validate and canonicalize context file if provided
    canonical_context: str | None = None
    if context_file:
        canonical_context = _canonicalize_path(context_file)
        if not os.path.exists(canonical_context):
            return FormalizeResult(
                status="error",
                message=f"Context file not found: {context_file}",
            )

    try:
        from aristotlelib import Project, ProjectInputType

        # Create a temp file with the natural language description
        with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
            f.write(description)
            temp_path = f.name

        try:
            # Use informal input type for natural language (async)
            result_path = await Project.prove_from_file(
                input_file_path=temp_path,
                project_input_type=ProjectInputType.INFORMAL,
                formal_input_context=canonical_context,
                wait_for_completion=True,
            )

            if result_path and os.path.exists(result_path):
                with open(result_path) as f:
                    lean_code = f.read()

                # Check if it was proved (no sorries remaining)
                has_sorry = _count_sorries(lean_code) > 0
                if prove and has_sorry:
                    status = "formalized"  # Formalized but not proved
                elif prove and not has_sorry:
                    status = "proved"
                else:
                    status = "formalized"

                msg = "Successfully formalized"
                if status == "proved":
                    msg += " and proved"
                return FormalizeResult(
                    status=status,
                    lean_code=lean_code,
                    message=msg,
                )
            else:
                return FormalizeResult(
                    status="failed",
                    message="Could not formalize the statement",
                )
        finally:
            os.unlink(temp_path)

    except Exception as e:
        return FormalizeResult(
            status="error",
            message=_sanitize_api_error(e),
        )
