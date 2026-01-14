"""Tool implementations for the Aristotle MCP server."""

from __future__ import annotations

import os
import re
import tempfile
from dataclasses import dataclass

from dotenv import load_dotenv

from aristotle_mcp.mock import (
    mock_check_proof,
    mock_check_prove_file,
    mock_formalize,
    mock_prove,
    mock_prove_file,
)

# Regex for counting sorry statements (word boundary to avoid matching "sorryExample")
_SORRY_PATTERN = re.compile(r"\bsorry\b")


def _count_sorries(text: str) -> int:
    """Count sorry statements in text using word boundary matching."""
    matches: list[str] = _SORRY_PATTERN.findall(text)
    return len(matches)

# Type for JSON-serializable result dictionaries
ResultValue = str | int | None
ResultDict = dict[str, ResultValue]

# Track whether .env has been loaded
_dotenv_loaded = False

# Metadata store for async proof jobs (persists across polls within server lifetime)
# Maps project_id -> metadata dict
_async_job_metadata: dict[str, dict[str, str | int]] = {}


def _find_unique_path(path: str, max_attempts: int = 1000) -> str:
    """Find a unique path by adding a number suffix if the file exists.

    Example: foo_aristotle.lean -> foo_aristotle.1.lean -> foo_aristotle.2.lean

    Args:
        path: The base path to check
        max_attempts: Maximum number of suffixes to try before raising

    Returns:
        A path that doesn't exist

    Raises:
        RuntimeError: If no unique path found within max_attempts
    """
    if not os.path.exists(path):
        return path

    base, ext = os.path.splitext(path)
    for counter in range(1, max_attempts + 1):
        new_path = f"{base}.{counter}{ext}"
        if not os.path.exists(new_path):
            return new_path

    raise RuntimeError(f"Could not find unique path after {max_attempts} attempts: {path}")


def _ensure_dotenv() -> None:
    """Load .env file if not already loaded."""
    global _dotenv_loaded
    if not _dotenv_loaded:
        load_dotenv()
        _dotenv_loaded = True


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


@dataclass
class ProveResult:
    """Result from a prove operation."""

    status: str  # proved | counterexample | failed | error | submitted | in_progress | queued
    code: str | None = None
    counterexample: str | None = None
    project_id: str | None = None
    percent_complete: int | None = None
    message: str = ""

    def to_dict(self) -> ResultDict:
        """Convert to dictionary for JSON serialization."""
        result: ResultDict = {"status": self.status, "message": self.message}
        if self.code is not None:
            result["code"] = self.code
        if self.counterexample is not None:
            result["counterexample"] = self.counterexample
        if self.project_id is not None:
            result["project_id"] = self.project_id
        if self.percent_complete is not None:
            result["percent_complete"] = self.percent_complete
        return result


@dataclass
class ProveFileResult:
    """Result from a prove_file operation."""

    status: str  # proved | partial | failed | error | submitted | in_progress | queued
    output_path: str | None = None
    sorries_filled: int = 0
    sorries_total: int = 0
    project_id: str | None = None
    percent_complete: int | None = None
    message: str = ""

    def to_dict(self) -> ResultDict:
        """Convert to dictionary for JSON serialization."""
        result: ResultDict = {
            "status": self.status,
            "sorries_filled": self.sorries_filled,
            "sorries_total": self.sorries_total,
            "message": self.message,
        }
        if self.output_path is not None:
            result["output_path"] = self.output_path
        if self.project_id is not None:
            result["project_id"] = self.project_id
        if self.percent_complete is not None:
            result["percent_complete"] = self.percent_complete
        return result


@dataclass
class FormalizeResult:
    """Result from a formalize operation."""

    status: str  # formalized | proved | failed | error
    lean_code: str | None = None
    message: str = ""

    def to_dict(self) -> ResultDict:
        """Convert to dictionary for JSON serialization."""
        result: ResultDict = {"status": self.status, "message": self.message}
        if self.lean_code is not None:
            result["lean_code"] = self.lean_code
        return result


async def prove(
    code: str,
    context_files: list[str] | None = None,
    hint: str | None = None,
    wait: bool = True,
) -> ProveResult:
    """
    Attempt to prove Lean code containing sorry statements.

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
    if is_mock_mode():
        mock_result = mock_prove(code, context_files, hint, wait=wait)
        return ProveResult(
            status=mock_result.status,
            code=mock_result.code,
            counterexample=mock_result.counterexample,
            project_id=mock_result.project_id,
            percent_complete=mock_result.percent_complete,
            message=mock_result.message,
        )

    # Real API implementation
    if not has_api_key():
        return ProveResult(
            status="error",
            message=(
                "ARISTOTLE_API_KEY environment variable not set. "
                "Set ARISTOTLE_MOCK=true for testing."
            ),
        )

    # Validate context files exist before making API calls
    if context_files:
        for ctx_file in context_files:
            if not os.path.exists(ctx_file):
                return ProveResult(
                    status="error",
                    message=f"Context file not found: {ctx_file}",
                )

    try:
        from aristotlelib import Project

        # Create project (async)
        project = await Project.create()

        # Add context files if provided (async)
        if context_files:
            await project.add_context(context_files)

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
            message=f"API error: {error_msg}",
        )


async def check_proof(project_id: str) -> ProveResult:
    """
    Check the status of a previously submitted proof.

    Args:
        project_id: The project ID returned from prove(wait=False)

    Returns:
        ProveResult with current status. If complete, includes the proof code.
    """
    if is_mock_mode():
        mock_result = mock_check_proof(project_id)
        return ProveResult(
            status=mock_result.status,
            code=mock_result.code,
            counterexample=mock_result.counterexample,
            project_id=mock_result.project_id,
            percent_complete=mock_result.percent_complete,
            message=mock_result.message,
        )

    if not has_api_key():
        return ProveResult(
            status="error",
            message="ARISTOTLE_API_KEY environment variable not set.",
        )

    try:
        from aristotlelib import Project

        # Load existing project
        project = await Project.from_id(project_id)
        await project.refresh()

        # Get status name from enum (e.g., ProjectStatus.QUEUED -> "QUEUED")
        status_str = (
            project.status.name if hasattr(project.status, "name") else str(project.status).upper()
        )

        # Get percent complete (may be None while queued)
        pct = project.percent_complete

        # Map API status to our status
        if status_str == "COMPLETE":
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

        elif status_str in ("QUEUED", "NOT_STARTED"):
            return ProveResult(
                status="queued",
                project_id=project_id,
                percent_complete=0,
                message="Proof is queued, waiting to start",
            )

        elif status_str == "IN_PROGRESS":
            return ProveResult(
                status="in_progress",
                project_id=project_id,
                percent_complete=pct,
                message=f"Proof is being computed ({pct}% complete)",
            )

        elif status_str == "PENDING_RETRY":
            return ProveResult(
                status="in_progress",
                project_id=project_id,
                percent_complete=pct,
                message="Proof is pending retry",
            )

        elif status_str == "FAILED":
            return ProveResult(
                status="failed",
                project_id=project_id,
                percent_complete=pct,
                message="Proof failed",
            )

        else:
            return ProveResult(
                status="in_progress",
                project_id=project_id,
                percent_complete=pct,
                message=f"Status: {status_str}",
            )

    except Exception as e:
        return ProveResult(
            status="error",
            project_id=project_id,
            message=f"API error: {e!s}",
        )


async def prove_file(
    file_path: str,
    output_path: str | None = None,
    wait: bool = True,
) -> ProveFileResult:
    """
    Prove all sorry statements in a Lean file.

    Args:
        file_path: Path to Lean file with sorry statements
        output_path: Where to write solution (default: {file}_aristotle.lean)
        wait: If True (default), block until complete. If False, return immediately
              with a project_id that can be polled with check_prove_file.

    Returns:
        ProveFileResult with status and counts.
        If wait=False, returns status="submitted" with project_id for polling.
    """
    if not os.path.exists(file_path):
        return ProveFileResult(
            status="error",
            message=f"File not found: {file_path}",
        )

    # Determine the actual output path (matches aristotlelib's default naming)
    actual_output_path = output_path
    if actual_output_path is None:
        base, ext = os.path.splitext(file_path)
        actual_output_path = f"{base}_aristotle{ext}"

    # Check if output would overwrite existing file
    if os.path.exists(actual_output_path):
        return ProveFileResult(
            status="error",
            message=f"Output file already exists: {actual_output_path}",
        )

    # Count sorries in original file
    with open(file_path) as f:
        original = f.read()
    original_sorries = _count_sorries(original)

    if is_mock_mode():
        mock_result = mock_prove_file(file_path, output_path, wait=wait)
        return ProveFileResult(
            status=mock_result.status,
            output_path=mock_result.output_path,
            sorries_filled=mock_result.sorries_filled,
            sorries_total=mock_result.sorries_total,
            project_id=mock_result.project_id,
            percent_complete=mock_result.percent_complete,
            message=mock_result.message,
        )

    # Real API implementation
    if not has_api_key():
        return ProveFileResult(
            status="error",
            message=(
                "ARISTOTLE_API_KEY environment variable not set. "
                "Set ARISTOTLE_MOCK=true for testing."
            ),
        )

    try:
        from aristotlelib import Project, ProjectStatus

        # Use prove_from_file for both sync and async modes
        # This ensures auto_add_imports is used to handle local dependencies
        result = await Project.prove_from_file(
            input_file_path=file_path,
            output_file_path=actual_output_path,
            auto_add_imports=True,
            wait_for_completion=wait,
        )

        # For async mode, we need to find the project_id for polling
        if not wait:
            # List recent projects to find the one we just created
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

            # Store metadata for retrieval when polling
            _async_job_metadata[project_id] = {
                "file_path": os.path.abspath(file_path),
                "output_path": actual_output_path,
                "sorries_total": original_sorries,
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
            message=f"API error: {e!s}",
        )


async def check_prove_file(project_id: str, output_path: str | None = None) -> ProveFileResult:
    """
    Check the status of a previously submitted file proof.

    Args:
        project_id: The project ID returned from prove_file(wait=False)
        output_path: Where to write solution when complete (optional)

    Returns:
        ProveFileResult with current status. If complete, includes output_path and counts.
    """
    if is_mock_mode():
        mock_result = mock_check_prove_file(project_id)
        return ProveFileResult(
            status=mock_result.status,
            output_path=mock_result.output_path,
            sorries_filled=mock_result.sorries_filled,
            sorries_total=mock_result.sorries_total,
            project_id=mock_result.project_id,
            percent_complete=mock_result.percent_complete,
            message=mock_result.message,
        )

    if not has_api_key():
        return ProveFileResult(
            status="error",
            message="ARISTOTLE_API_KEY environment variable not set.",
        )

    # Retrieve stored metadata if available
    metadata = _async_job_metadata.get(project_id, {})
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

        if status_str == "COMPLETE":
            # Find a unique path to avoid overwriting existing files
            safe_output_path = _find_unique_path(output_path) if output_path else None

            # Get the solution
            solution_path = await project.get_solution(output_path=safe_output_path)

            # Clean up metadata now that job is complete
            _async_job_metadata.pop(project_id, None)

            sorries_total = int(stored_sorries_total) if stored_sorries_total else 0
            return _analyze_solution_file(str(solution_path), sorries_total, project_id)

        elif status_str in ("QUEUED", "NOT_STARTED"):
            return ProveFileResult(
                status="queued",
                project_id=project_id,
                percent_complete=0,
                message="Proof is queued, waiting to start",
            )

        elif status_str == "IN_PROGRESS":
            return ProveFileResult(
                status="in_progress",
                project_id=project_id,
                percent_complete=pct,
                message=f"Proof is being computed ({pct}% complete)",
            )

        elif status_str == "PENDING_RETRY":
            return ProveFileResult(
                status="in_progress",
                project_id=project_id,
                percent_complete=pct,
                message="Proof is pending retry",
            )

        elif status_str == "FAILED":
            # Clean up metadata for failed jobs
            _async_job_metadata.pop(project_id, None)
            return ProveFileResult(
                status="failed",
                project_id=project_id,
                percent_complete=pct,
                message="Proof failed",
            )

        else:
            return ProveFileResult(
                status="in_progress",
                project_id=project_id,
                percent_complete=pct,
                message=f"Status: {status_str}",
            )

    except Exception as e:
        return ProveFileResult(
            status="error",
            project_id=project_id,
            message=f"API error: {e!s}",
        )


async def formalize(
    description: str,
    prove: bool = False,
    context_file: str | None = None,
) -> FormalizeResult:
    """
    Convert natural language math to Lean 4 code.

    Args:
        description: Natural language math statement or problem
        prove: Whether to also prove the formalized statement
        context_file: Optional path to a Lean file providing definitions and context
                      for the formalization

    Returns:
        FormalizeResult with status and Lean code
    """
    if is_mock_mode():
        mock_result = mock_formalize(description, prove, context_file)
        return FormalizeResult(
            status=mock_result.status,
            lean_code=mock_result.lean_code,
            message=mock_result.message,
        )

    # Real API implementation
    if not has_api_key():
        return FormalizeResult(
            status="error",
            message=(
                "ARISTOTLE_API_KEY environment variable not set. "
                "Set ARISTOTLE_MOCK=true for testing."
            ),
        )

    # Validate context file if provided
    if context_file and not os.path.exists(context_file):
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
                formal_input_context=context_file,
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
            message=f"API error: {e!s}",
        )
