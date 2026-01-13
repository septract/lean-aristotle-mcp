"""Mock responses for testing without the Aristotle API."""

from __future__ import annotations

import re
import uuid
from dataclasses import dataclass
from typing import TypedDict

# In-memory store for mock async proofs
_mock_projects: dict[str, MockProjectData] = {}
_mock_file_projects: dict[str, MockFileProjectData] = {}


class MockProjectData(TypedDict):
    """Internal storage for mock proof jobs."""

    status: str
    code: str | None
    counterexample: str | None
    message: str
    poll_count: int


class MockFileProjectData(TypedDict):
    """Internal storage for mock file proof jobs."""

    status: str
    output_path: str | None
    sorries_filled: int
    sorries_total: int
    message: str
    poll_count: int


@dataclass
class MockProveResult:
    """Result from mock prove operation."""

    status: str
    code: str | None = None
    counterexample: str | None = None
    project_id: str | None = None
    percent_complete: int | None = None
    message: str = ""


@dataclass
class MockProveFileResult:
    """Result from mock prove_file operation."""

    status: str
    output_path: str | None = None
    sorries_filled: int = 0
    sorries_total: int = 0
    project_id: str | None = None
    percent_complete: int | None = None
    message: str = ""


@dataclass
class MockFormalizeResult:
    """Result from mock formalize operation."""

    status: str
    lean_code: str | None = None
    message: str = ""


def mock_prove(
    code: str,
    context_files: list[str] | None = None,
    hint: str | None = None,
    wait: bool = True,
) -> MockProveResult:
    """
    Mock implementation of prove.

    Provides realistic responses based on the input:
    - If code contains 'false_theorem' or 'bad_lemma': returns counterexample
    - If code contains 'timeout' or 'hard': returns failed
    - Otherwise: returns proved with sorries filled

    If wait=False, stores the proof job and returns a project_id for polling.

    Args:
        code: Lean 4 code containing sorry statements
        context_files: Optional paths to context files (unused in mock)
        hint: Optional hint (unused in mock)
        wait: If True, return result immediately. If False, return project_id for polling.

    Returns:
        MockProveResult with status and optional code/counterexample
    """
    # Silence unused argument warnings - these are part of the API
    _ = context_files
    _ = hint

    # Count sorries in the input
    sorry_count = len(tuple(re.finditer(r"\bsorry\b", code)))

    if sorry_count == 0:
        return MockProveResult(
            status="error", message="No 'sorry' statements found in the provided code"
        )

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
        final_code = re.sub(
            r"\bsorry\b",
            "simp [add_comm, add_assoc, mul_comm]  -- filled by Aristotle",
            code,
        )
        final_counterexample = None
        final_message = f"Successfully filled {sorry_count} sorry statement(s)"

    # Generate a project ID
    project_id = f"mock-{uuid.uuid4()}"

    # If not waiting, store the job and return immediately
    if not wait:
        _mock_projects[project_id] = MockProjectData(
            status=final_status,
            code=final_code,
            counterexample=final_counterexample,
            message=final_message,
            poll_count=0,
        )
        return MockProveResult(
            status="submitted",
            project_id=project_id,
            message="Proof submitted. Use check_proof to poll for results.",
        )

    # Waiting - return the final result immediately
    return MockProveResult(
        status=final_status,
        code=final_code,
        counterexample=final_counterexample,
        project_id=project_id,
        message=final_message,
    )


def mock_check_proof(project_id: str) -> MockProveResult:
    """
    Mock implementation of check_proof.

    Simulates async polling:
    - First call: returns "queued"
    - Second call: returns "in_progress"
    - Third+ calls: returns the final result

    Args:
        project_id: The mock project ID to check

    Returns:
        MockProveResult with current status
    """
    if project_id not in _mock_projects:
        return MockProveResult(
            status="error",
            project_id=project_id,
            message=f"Unknown project ID: {project_id}",
        )

    project = _mock_projects[project_id]
    project["poll_count"] += 1

    # Simulate progression through statuses
    if project["poll_count"] == 1:
        return MockProveResult(
            status="queued",
            project_id=project_id,
            percent_complete=0,
            message="Proof is queued, waiting to start",
        )
    elif project["poll_count"] == 2:
        return MockProveResult(
            status="in_progress",
            project_id=project_id,
            percent_complete=50,
            message="Proof is being computed (50% complete)",
        )
    else:
        # Return final result
        return MockProveResult(
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
) -> MockProveFileResult:
    """
    Mock implementation of prove_file.

    Returns a simulated result based on the file path.

    Args:
        file_path: Path to the Lean file
        output_path: Optional output path for the solved file
        wait: If True, return result immediately. If False, return project_id for polling.

    Returns:
        MockProveFileResult with status and counts
    """
    import os

    if not os.path.exists(file_path):
        return MockProveFileResult(status="error", message=f"File not found: {file_path}")

    # Read the file to count sorries
    with open(file_path) as f:
        content = f.read()

    sorry_count = len(tuple(re.finditer(r"\bsorry\b", content)))

    if sorry_count == 0:
        return MockProveFileResult(
            status="error", sorries_total=0, message="No 'sorry' statements found in the file"
        )

    # Determine output path
    if output_path is None:
        base, ext = os.path.splitext(file_path)
        output_path = f"{base}.solved{ext}"

    # Determine final result
    if sorry_count > 5:
        final_status = "partial"
        filled = sorry_count - 2
        final_message = f"Filled {filled} of {sorry_count} sorry statements"
    else:
        final_status = "proved"
        filled = sorry_count
        final_message = f"Successfully filled all {sorry_count} sorry statement(s)"

    # Generate project ID
    project_id = f"mock-file-{uuid.uuid4()}"

    # If not waiting, store the job and return immediately
    if not wait:
        _mock_file_projects[project_id] = MockFileProjectData(
            status=final_status,
            output_path=output_path,
            sorries_filled=filled,
            sorries_total=sorry_count,
            message=final_message,
            poll_count=0,
        )
        return MockProveFileResult(
            status="submitted",
            sorries_total=sorry_count,
            project_id=project_id,
            message="Proof submitted. Use check_prove_file to poll for results.",
        )

    # Waiting - return final result
    return MockProveFileResult(
        status=final_status,
        output_path=output_path,
        sorries_filled=filled,
        sorries_total=sorry_count,
        project_id=project_id,
        percent_complete=100,
        message=final_message,
    )


def mock_check_prove_file(project_id: str) -> MockProveFileResult:
    """
    Mock implementation of check_prove_file.

    Simulates async polling for file proofs:
    - First call: returns "queued"
    - Second call: returns "in_progress"
    - Third+ calls: returns the final result

    Args:
        project_id: The mock project ID to check

    Returns:
        MockProveFileResult with current status
    """
    if project_id not in _mock_file_projects:
        return MockProveFileResult(
            status="error",
            project_id=project_id,
            message=f"Unknown project ID: {project_id}",
        )

    project = _mock_file_projects[project_id]
    project["poll_count"] += 1

    # Simulate progression through statuses
    if project["poll_count"] == 1:
        return MockProveFileResult(
            status="queued",
            sorries_total=project["sorries_total"],
            project_id=project_id,
            percent_complete=0,
            message="Proof is queued, waiting to start",
        )
    elif project["poll_count"] == 2:
        return MockProveFileResult(
            status="in_progress",
            sorries_total=project["sorries_total"],
            project_id=project_id,
            percent_complete=50,
            message="Proof is being computed (50% complete)",
        )
    else:
        # Return final result
        return MockProveFileResult(
            status=project["status"],
            output_path=project["output_path"],
            sorries_filled=project["sorries_filled"],
            sorries_total=project["sorries_total"],
            project_id=project_id,
            percent_complete=100,
            message=project["message"],
        )


def mock_formalize(
    description: str,
    prove: bool = False,
    context_file: str | None = None,
) -> MockFormalizeResult:
    """
    Mock implementation of formalize.

    Generates plausible Lean code from natural language descriptions.

    Args:
        description: Natural language description of the theorem
        prove: Whether to also prove the formalized statement
        context_file: Optional Lean file providing context definitions

    Returns:
        MockFormalizeResult with status and Lean code
    """
    description_lower = description.lower()

    # Add context import if provided
    context_header = ""
    if context_file:
        import os

        context_name = os.path.splitext(os.path.basename(context_file))[0]
        context_header = f"-- Using context from: {context_file}\nimport {context_name}\n\n"

    # Generate different formalizations based on keywords
    if "even" in description_lower and "sum" in description_lower:
        lean_code = """def even (n : Nat) : Prop := ∃ k, n = 2 * k

theorem sum_of_evens (a b : Nat) (ha : even a) (hb : even b) : even (a + b) := by
  sorry"""
        if prove:
            lean_code = lean_code.replace(
                "sorry",
                "obtain ⟨ka, hka⟩ := ha; obtain ⟨kb, hkb⟩ := hb; exact ⟨ka + kb, by omega⟩",
            )

    elif "prime" in description_lower:
        lean_code = """def prime (n : Nat) : Prop := n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

theorem prime_example : prime 7 := by
  sorry"""
        if prove:
            lean_code = lean_code.replace("sorry", "decide")

    elif "commut" in description_lower:
        lean_code = """theorem add_comm_example (a b : Nat) : a + b = b + a := by
  sorry"""
        if prove:
            lean_code = lean_code.replace("sorry", "ring")

    else:
        # Generic formalization
        lean_code = f"""-- Formalization of: {description}
theorem statement : True := by
  sorry"""
        if prove:
            lean_code = lean_code.replace("sorry", "trivial")

    lean_code = context_header + lean_code
    status = "proved" if prove else "formalized"
    message = "Formalized and proved" if prove else "Successfully formalized to Lean 4"
    if context_file:
        message += f" (using context from {context_file})"

    return MockFormalizeResult(status=status, lean_code=lean_code, message=message)
