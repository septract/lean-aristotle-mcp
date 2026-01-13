"""Mock responses for testing without the Aristotle API."""

from __future__ import annotations

import re
import uuid
from dataclasses import dataclass
from typing import TypedDict

# In-memory store for mock async proofs
_mock_projects: dict[str, MockProjectData] = {}


class MockProjectData(TypedDict):
    """Internal storage for mock proof jobs."""

    status: str
    code: str | None
    counterexample: str | None
    message: str
    poll_count: int


@dataclass
class MockProveResult:
    """Result from mock prove operation."""

    status: str
    code: str | None = None
    counterexample: str | None = None
    project_id: str | None = None
    message: str = ""


@dataclass
class MockProveFileResult:
    """Result from mock prove_file operation."""

    status: str
    output_path: str | None = None
    sorries_filled: int = 0
    sorries_total: int = 0
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
    sorry_count = len(re.findall(r"\bsorry\b", code))

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
            message="Proof is queued, waiting to start",
        )
    elif project["poll_count"] == 2:
        return MockProveResult(
            status="in_progress",
            project_id=project_id,
            message="Proof is being computed",
        )
    else:
        # Return final result
        return MockProveResult(
            status=project["status"],
            code=project["code"],
            counterexample=project["counterexample"],
            project_id=project_id,
            message=project["message"],
        )


def mock_prove_file(file_path: str, output_path: str | None = None) -> MockProveFileResult:
    """
    Mock implementation of prove_file.

    Returns a simulated result based on the file path.

    Args:
        file_path: Path to the Lean file
        output_path: Optional output path for the solved file

    Returns:
        MockProveFileResult with status and counts
    """
    import os

    if not os.path.exists(file_path):
        return MockProveFileResult(status="error", message=f"File not found: {file_path}")

    # Read the file to count sorries
    with open(file_path) as f:
        content = f.read()

    sorry_count = len(re.findall(r"\bsorry\b", content))

    if sorry_count == 0:
        return MockProveFileResult(
            status="error", sorries_total=0, message="No 'sorry' statements found in the file"
        )

    # Determine output path
    if output_path is None:
        base, ext = os.path.splitext(file_path)
        output_path = f"{base}.solved{ext}"

    # Simulate partial success for files with many sorries
    if sorry_count > 5:
        filled = sorry_count - 2  # Simulate 2 unfilled
        return MockProveFileResult(
            status="partial",
            output_path=output_path,
            sorries_filled=filled,
            sorries_total=sorry_count,
            message=f"Filled {filled} of {sorry_count} sorry statements",
        )

    # Full success
    return MockProveFileResult(
        status="proved",
        output_path=output_path,
        sorries_filled=sorry_count,
        sorries_total=sorry_count,
        message=f"Successfully filled all {sorry_count} sorry statement(s)",
    )


def mock_formalize(description: str, prove: bool = False) -> MockFormalizeResult:
    """
    Mock implementation of formalize.

    Generates plausible Lean code from natural language descriptions.

    Args:
        description: Natural language description of the theorem
        prove: Whether to also prove the formalized statement

    Returns:
        MockFormalizeResult with status and Lean code
    """
    description_lower = description.lower()

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

    status = "proved" if prove else "formalized"
    message = "Formalized and proved" if prove else "Successfully formalized to Lean 4"

    return MockFormalizeResult(status=status, lean_code=lean_code, message=message)
