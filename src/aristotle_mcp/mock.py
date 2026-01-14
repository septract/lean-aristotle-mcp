"""Mock responses for testing without the Aristotle API."""

from __future__ import annotations

import os
import threading
import uuid
from typing import TypedDict

from aristotle_mcp.models import FormalizeResult, ProveFileResult, ProveResult

# Thread lock for accessing shared mock state
_mock_lock = threading.Lock()

# In-memory store for mock async proofs
# Access must be protected by _mock_lock
_mock_projects: dict[str, _MockProjectData] = {}
_mock_file_projects: dict[str, _MockFileProjectData] = {}
_mock_formalize_projects: dict[str, _MockFormalizeProjectData] = {}


class _MockProjectData(TypedDict):
    """Internal storage for mock proof jobs."""

    status: str
    code: str | None
    counterexample: str | None
    message: str
    poll_count: int


class _MockFileProjectData(TypedDict):
    """Internal storage for mock file proof jobs."""

    status: str
    output_path: str | None
    message: str
    poll_count: int


class _MockFormalizeProjectData(TypedDict):
    """Internal storage for mock formalize jobs."""

    status: str
    lean_code: str | None
    message: str
    poll_count: int


def mock_prove(
    code: str,
    context_files: list[str] | None = None,
    hint: str | None = None,
    wait: bool = True,
) -> ProveResult:
    """Mock implementation of prove.

    Provides realistic responses based on the input:
    - If code contains 'false_theorem' or 'bad_lemma': returns counterexample
    - If code contains 'timeout' or 'hard': returns failed
    - Otherwise: returns proved

    If wait=False, stores the proof job and returns a project_id for polling.

    Args:
        code: Lean 4 code containing sorry statements
        context_files: Optional paths to context files (unused in mock)
        hint: Optional hint (unused in mock)
        wait: If True, return result immediately. If False, return project_id for polling.

    Returns:
        ProveResult with status and optional code/counterexample
    """
    # Silence unused argument warnings - these are part of the API
    _ = context_files
    _ = hint

    # Determine what the final result will be
    final_code: str | None
    final_counterexample: str | None

    if "false_theorem" in code.lower() or "bad_lemma" in code.lower():
        final_status = "counterexample"
        final_code = None
        final_counterexample = (
            "n = 0 provides a counterexample: the left-hand side evaluates to 0, "
            "but the right-hand side evaluates to 1"
        )
        final_message = "Statement is false; counterexample found"
    elif "timeout" in code.lower() or "hard" in code.lower():
        final_status = "failed"
        final_code = None
        final_counterexample = None
        final_message = (
            "Could not find a proof within the time limit. "
            "This does not mean the statement is false."
        )
    else:
        final_status = "proved"
        # Return the code with a mock proof comment appended
        final_code = code + "\n-- Proof filled by Aristotle (mock)"
        final_counterexample = None
        final_message = "Successfully proved"

    # Generate a project ID
    project_id = f"mock-{uuid.uuid4()}"

    # If not waiting, store the job and return immediately (thread-safe)
    if not wait:
        with _mock_lock:
            _mock_projects[project_id] = _MockProjectData(
                status=final_status,
                code=final_code,
                counterexample=final_counterexample,
                message=final_message,
                poll_count=0,
            )
        return ProveResult(
            status="submitted",
            project_id=project_id,
            message="Proof submitted. Use check_proof to poll for results.",
        )

    # Waiting - return the final result immediately
    return ProveResult(
        status=final_status,
        code=final_code,
        counterexample=final_counterexample,
        project_id=project_id,
        message=final_message,
    )


def mock_check_proof(project_id: str) -> ProveResult:
    """Mock implementation of check_proof.

    Simulates async polling:
    - First call: returns "queued"
    - Second call: returns "in_progress"
    - Third+ calls: returns the final result

    Args:
        project_id: The mock project ID to check

    Returns:
        ProveResult with current status
    """
    with _mock_lock:
        if project_id not in _mock_projects:
            return ProveResult(
                status="error",
                project_id=project_id,
                message=f"Unknown project ID: {project_id}",
            )

        project = _mock_projects[project_id]
        project["poll_count"] += 1
        poll_count = project["poll_count"]

        # Simulate progression through statuses
        if poll_count == 1:
            return ProveResult(
                status="queued",
                project_id=project_id,
                percent_complete=0,
                message="Proof is queued, waiting to start",
            )
        elif poll_count == 2:
            return ProveResult(
                status="in_progress",
                project_id=project_id,
                percent_complete=50,
                message="Proof is being computed (50% complete)",
            )
        else:
            # Return final result
            return ProveResult(
                status=project["status"],
                code=project["code"],
                counterexample=project["counterexample"],
                project_id=project_id,
                percent_complete=100,
                message=project["message"],
            )


def mock_prove_file(
    file_path: str,
    output_path: str | None = None,
    wait: bool = True,
) -> ProveFileResult:
    """Mock implementation of prove_file.

    Returns a simulated result based on the file path.

    Args:
        file_path: Path to the Lean file
        output_path: Optional output path for the solved file
        wait: If True, return result immediately. If False, return project_id for polling.

    Returns:
        ProveFileResult with status
    """
    if not os.path.exists(file_path):
        return ProveFileResult(status="error", message=f"File not found: {file_path}")

    # Determine output path (matches aristotlelib's default naming)
    if output_path is None:
        base, ext = os.path.splitext(file_path)
        output_path = f"{base}_aristotle{ext}"

    # Check if output would overwrite existing file
    if os.path.exists(output_path):
        return ProveFileResult(
            status="error",
            message=f"Output file already exists: {output_path}",
        )

    # Determine final result based on filename for testing different scenarios
    if "partial" in file_path.lower():
        final_status = "partial"
        final_message = "Some proofs could not be completed"
    elif "fail" in file_path.lower():
        final_status = "failed"
        final_message = "Could not find proofs within the time limit"
    else:
        final_status = "proved"
        final_message = "Successfully proved"

    # Generate project ID
    project_id = f"mock-file-{uuid.uuid4()}"

    # If not waiting, store the job and return immediately (thread-safe)
    if not wait:
        with _mock_lock:
            _mock_file_projects[project_id] = _MockFileProjectData(
                status=final_status,
                output_path=output_path,
                message=final_message,
                poll_count=0,
            )
        return ProveFileResult(
            status="submitted",
            project_id=project_id,
            message="Proof submitted. Use check_prove_file to poll for results.",
        )

    # Waiting - return final result
    return ProveFileResult(
        status=final_status,
        output_path=output_path,
        project_id=project_id,
        percent_complete=100,
        message=final_message,
    )


def mock_check_prove_file(project_id: str) -> ProveFileResult:
    """Mock implementation of check_prove_file.

    Simulates async polling for file proofs:
    - First call: returns "queued"
    - Second call: returns "in_progress"
    - Third+ calls: returns the final result

    Args:
        project_id: The mock project ID to check

    Returns:
        ProveFileResult with current status
    """
    with _mock_lock:
        if project_id not in _mock_file_projects:
            return ProveFileResult(
                status="error",
                project_id=project_id,
                message=f"Unknown project ID: {project_id}",
            )

        project = _mock_file_projects[project_id]
        project["poll_count"] += 1
        poll_count = project["poll_count"]

        # Simulate progression through statuses
        if poll_count == 1:
            return ProveFileResult(
                status="queued",
                project_id=project_id,
                percent_complete=0,
                message="Proof is queued, waiting to start",
            )
        elif poll_count == 2:
            return ProveFileResult(
                status="in_progress",
                project_id=project_id,
                percent_complete=50,
                message="Proof is being computed (50% complete)",
            )
        else:
            # Return final result
            return ProveFileResult(
                status=project["status"],
                output_path=project["output_path"],
                project_id=project_id,
                percent_complete=100,
                message=project["message"],
            )


def _generate_mock_lean_code(
    description: str,
    prove: bool,
    context_file: str | None,
) -> tuple[str, str, str]:
    """Generate mock Lean code based on description keywords.

    Returns:
        Tuple of (lean_code, status, message)
    """
    # Add context import if provided
    context_header = ""
    if context_file:
        context_name = os.path.splitext(os.path.basename(context_file))[0]
        context_header = f"-- Using context from: {context_file}\nimport {context_name}\n\n"

    description_lower = description.lower()

    # Generate different formalizations based on keywords
    if "even" in description_lower and "sum" in description_lower:
        if prove:
            lean_code = """def even (n : Nat) : Prop := ∃ k, n = 2 * k

theorem sum_of_evens (a b : Nat) (ha : even a) (hb : even b) : even (a + b) := by
  obtain ⟨ka, hka⟩ := ha; obtain ⟨kb, hkb⟩ := hb; exact ⟨ka + kb, by omega⟩"""
        else:
            lean_code = """def even (n : Nat) : Prop := ∃ k, n = 2 * k

theorem sum_of_evens (a b : Nat) (ha : even a) (hb : even b) : even (a + b) := by
  sorry"""

    elif "prime" in description_lower:
        if prove:
            lean_code = """def prime (n : Nat) : Prop := n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

theorem prime_example : prime 7 := by
  decide"""
        else:
            lean_code = """def prime (n : Nat) : Prop := n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

theorem prime_example : prime 7 := by
  sorry"""

    elif "commut" in description_lower:
        if prove:
            lean_code = """theorem add_comm_example (a b : Nat) : a + b = b + a := by
  ring"""
        else:
            lean_code = """theorem add_comm_example (a b : Nat) : a + b = b + a := by
  sorry"""

    else:
        # Generic formalization
        if prove:
            lean_code = f"""-- Formalization of: {description}
theorem statement : True := by
  trivial"""
        else:
            lean_code = f"""-- Formalization of: {description}
theorem statement : True := by
  sorry"""

    lean_code = context_header + lean_code
    status = "proved" if prove else "formalized"
    message = "Formalized and proved" if prove else "Successfully formalized to Lean 4"
    if context_file:
        message += f" (using context from {context_file})"

    return lean_code, status, message


def mock_formalize(
    description: str,
    prove: bool = False,
    context_file: str | None = None,
    wait: bool = True,
) -> FormalizeResult:
    """Mock implementation of formalize.

    Generates plausible Lean code from natural language descriptions.

    Args:
        description: Natural language description of the theorem
        prove: Whether to also prove the formalized statement
        context_file: Optional Lean file providing context definitions
        wait: If True, return result immediately. If False, return project_id for polling.

    Returns:
        FormalizeResult with status and Lean code
    """
    lean_code, final_status, final_message = _generate_mock_lean_code(
        description, prove, context_file
    )

    # Generate project ID
    project_id = f"mock-formalize-{uuid.uuid4()}"

    # If not waiting, store the job and return immediately (thread-safe)
    if not wait:
        with _mock_lock:
            _mock_formalize_projects[project_id] = _MockFormalizeProjectData(
                status=final_status,
                lean_code=lean_code,
                message=final_message,
                poll_count=0,
            )
        return FormalizeResult(
            status="submitted",
            project_id=project_id,
            message="Formalization submitted. Use check_formalize to poll for results.",
        )

    # Waiting - return final result immediately
    return FormalizeResult(
        status=final_status,
        lean_code=lean_code,
        project_id=project_id,
        message=final_message,
    )


def mock_check_formalize(project_id: str) -> FormalizeResult:
    """Mock implementation of check_formalize.

    Simulates async polling for formalization jobs:
    - First call: returns "queued"
    - Second call: returns "in_progress"
    - Third+ calls: returns the final result

    Args:
        project_id: The mock project ID to check

    Returns:
        FormalizeResult with current status
    """
    with _mock_lock:
        if project_id not in _mock_formalize_projects:
            return FormalizeResult(
                status="error",
                project_id=project_id,
                message=f"Unknown project ID: {project_id}",
            )

        project = _mock_formalize_projects[project_id]
        project["poll_count"] += 1
        poll_count = project["poll_count"]

        # Simulate progression through statuses
        if poll_count == 1:
            return FormalizeResult(
                status="queued",
                project_id=project_id,
                percent_complete=0,
                message="Formalization is queued, waiting to start",
            )
        elif poll_count == 2:
            return FormalizeResult(
                status="in_progress",
                project_id=project_id,
                percent_complete=50,
                message="Formalization is being computed (50% complete)",
            )
        else:
            # Return final result
            return FormalizeResult(
                status=project["status"],
                lean_code=project["lean_code"],
                project_id=project_id,
                percent_complete=100,
                message=project["message"],
            )
