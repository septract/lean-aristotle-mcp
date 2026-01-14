"""Test the Aristotle MCP tools in mock mode."""

import os
from pathlib import Path

import pytest

# Force mock mode for these tests
os.environ["ARISTOTLE_MOCK"] = "true"

from aristotle_mcp.tools import (
    check_proof,
    check_prove_file,
    formalize,
    is_mock_mode,
    prove,
    prove_file,
)

FIXTURES_DIR = Path(__file__).parent / "fixtures"
LEAN_PROJECT_DIR = Path(__file__).parent / "lean_project"


@pytest.fixture
def example_lean_file() -> Path:
    return FIXTURES_DIR / "example.lean"


@pytest.fixture
def lean_project_file() -> Path:
    return LEAN_PROJECT_DIR / "TestProject" / "Arithmetic.lean"


def test_mock_mode_enabled() -> None:
    """Verify mock mode is active."""
    assert is_mock_mode()


async def test_prove_simple() -> None:
    """Test proving a simple theorem."""
    code = "theorem one_plus_one : 1 + 1 = 2 := by sorry"
    result = await prove(code)

    assert result.status == "proved"
    assert result.code is not None
    assert "sorry" not in result.code
    assert result.message


async def test_prove_with_hint() -> None:
    """Test proving with a hint."""
    code = "theorem add_comm (a b : Nat) : a + b = b + a := by sorry"
    result = await prove(code, hint="Use induction on a")

    assert result.status == "proved"
    assert result.code is not None


async def test_prove_counterexample() -> None:
    """Test that false theorems return counterexamples."""
    code = "theorem false_theorem : 1 = 2 := by sorry"
    result = await prove(code)

    assert result.status == "counterexample"
    assert result.counterexample is not None


async def test_prove_async_flow() -> None:
    """Test async submission and polling."""
    code = "theorem async_test : 1 + 1 = 2 := by sorry"

    # Submit without waiting
    result = await prove(code, wait=False)
    assert result.status == "submitted"
    assert result.project_id is not None

    project_id = result.project_id

    # First poll - should be queued or in_progress
    result = await check_proof(project_id)
    assert result.status in ("queued", "in_progress", "proved")
    assert result.project_id == project_id

    # Keep polling until complete (mock progresses each call)
    for _ in range(5):
        result = await check_proof(project_id)
        if result.status == "proved":
            break

    assert result.status == "proved"
    assert result.code is not None


async def test_check_proof_percent_complete() -> None:
    """Test that check_proof returns percent_complete."""
    code = "theorem pct_test : 1 + 1 = 2 := by sorry"

    # Submit
    result = await prove(code, wait=False)
    project_id = result.project_id
    assert project_id is not None

    # First poll - queued, 0%
    result = await check_proof(project_id)
    assert result.status == "queued"
    assert result.percent_complete == 0

    # Second poll - in_progress, 50%
    result = await check_proof(project_id)
    assert result.status == "in_progress"
    assert result.percent_complete == 50

    # Third poll - proved, 100%
    result = await check_proof(project_id)
    assert result.status == "proved"
    assert result.percent_complete == 100


async def test_prove_file(example_lean_file: Path) -> None:
    """Test proving all sorries in a file."""
    result = await prove_file(str(example_lean_file))

    assert result.status in ("proved", "partial")
    assert result.sorries_total > 0
    assert result.sorries_filled > 0
    assert result.message


async def test_prove_file_async(example_lean_file: Path) -> None:
    """Test async file proving with polling."""
    # Submit without waiting
    result = await prove_file(str(example_lean_file), wait=False)
    assert result.status == "submitted"
    assert result.project_id is not None
    assert result.sorries_total > 0

    project_id = result.project_id

    # First poll - queued
    result = await check_prove_file(project_id)
    assert result.status == "queued"
    assert result.percent_complete == 0

    # Second poll - in_progress
    result = await check_prove_file(project_id)
    assert result.status == "in_progress"
    assert result.percent_complete == 50

    # Third poll - complete
    result = await check_prove_file(project_id)
    assert result.status in ("proved", "partial")
    assert result.percent_complete == 100
    assert result.sorries_filled > 0


async def test_prove_file_not_found() -> None:
    """Test error handling for missing files."""
    result = await prove_file("/nonexistent/file.lean")

    assert result.status == "error"
    assert "not found" in result.message.lower()


async def test_prove_file_output_exists(example_lean_file: Path, tmp_path: Path) -> None:
    """Test error when output file already exists."""
    # Use tmp_path to avoid touching any real files
    test_output_path = tmp_path / "existing_output.lean"
    test_output_path.write_text("-- existing file for test")

    result = await prove_file(str(example_lean_file), output_path=str(test_output_path))

    assert result.status == "error"
    assert "already exists" in result.message.lower()
    # tmp_path is automatically cleaned up by pytest


async def test_prove_lean_project(lean_project_file: Path, tmp_path: Path) -> None:
    """Test proving a file from the lean_project test fixture."""
    # Use tmp_path for output to avoid touching any real files
    test_output_path = tmp_path / "Arithmetic_solved.lean"

    result = await prove_file(str(lean_project_file), output_path=str(test_output_path))

    assert result.status in ("proved", "partial")
    assert result.sorries_total == 4  # 4 theorems with sorry
    assert result.sorries_filled == 4  # Mock fills all (< 5 sorries)
    assert result.output_path is not None
    # tmp_path is automatically cleaned up by pytest


async def test_formalize() -> None:
    """Test formalizing natural language."""
    result = await formalize("The sum of two even numbers is even")

    assert result.status == "formalized"
    assert result.lean_code is not None
    assert "theorem" in result.lean_code.lower() or "def" in result.lean_code.lower()


async def test_formalize_and_prove() -> None:
    """Test formalizing and proving."""
    result = await formalize("1 + 1 = 2", prove=True)

    assert result.status == "proved"
    assert result.lean_code is not None


async def test_formalize_with_context(example_lean_file: Path) -> None:
    """Test formalizing with a context file."""
    result = await formalize(
        "Prove something using the definitions",
        context_file=str(example_lean_file),
    )

    assert result.status == "formalized"
    assert result.lean_code is not None
    assert "example" in result.lean_code.lower()  # Should reference the context file
    assert "context" in result.message.lower()
