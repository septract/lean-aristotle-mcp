"""Live API tests for MCP tool functions.

These tests validate our tool implementations against the real Aristotle API.
They are SKIPPED by default - run explicitly with:

    pytest tests/test_api_tools.py -v

Requires ARISTOTLE_API_KEY to be set. Tests are slow (proofs take 30-120s).
"""

import os

import pytest
from dotenv import load_dotenv

load_dotenv()

# Skip entire module if no API key or if ARISTOTLE_MOCK is set
pytestmark = [
    pytest.mark.skipif(
        not os.environ.get("ARISTOTLE_API_KEY"),
        reason="ARISTOTLE_API_KEY not set",
    ),
    pytest.mark.skipif(
        os.environ.get("ARISTOTLE_MOCK", "").lower() in ("true", "1", "yes"),
        reason="ARISTOTLE_MOCK is enabled - disable for live API tests",
    ),
]


# Import tools after skip checks to avoid import errors when aristotlelib not installed
@pytest.fixture
def tools():
    """Import tools module."""
    from aristotle_mcp import tools

    return tools


@pytest.fixture
def simple_code() -> str:
    """Simple theorem that should prove quickly."""
    return "theorem simple : 1 + 1 = 2 := by sorry"


@pytest.fixture
def lean_file(tmp_path) -> str:
    """Create a temporary Lean file with sorries."""
    content = """
theorem test_add : 2 + 2 = 4 := by sorry

theorem test_comm (a b : Nat) : a + b = b + a := by sorry
"""
    path = tmp_path / "test.lean"
    path.write_text(content)
    return str(path)


class TestProveSync:
    """Test prove() with wait=True (synchronous)."""

    @pytest.mark.timeout(180)
    async def test_prove_simple(self, tools, simple_code: str) -> None:
        """Test proving a simple theorem synchronously."""
        result = await tools.prove(code=simple_code, wait=True)

        print(f"\nStatus: {result.status}")
        print(f"Message: {result.message}")
        if result.code:
            print(f"Code:\n{result.code}")

        assert result.status == "proved", f"Expected proved, got {result.status}: {result.message}"
        assert result.code is not None
        assert "sorry" not in result.code.lower() or "proved" in result.code.lower()
        assert result.project_id is not None


class TestProveAsync:
    """Test prove() with wait=False (asynchronous polling)."""

    @pytest.mark.timeout(180)
    async def test_prove_async_flow(self, tools, simple_code: str) -> None:
        """Test the full async flow: submit, poll, get result."""
        import asyncio

        # Submit
        submit_result = await tools.prove(code=simple_code, wait=False)

        print(f"\nSubmit status: {submit_result.status}")
        print(f"Project ID: {submit_result.project_id}")

        assert submit_result.status == "submitted"
        assert submit_result.project_id is not None

        project_id = submit_result.project_id

        # Poll until complete
        final_result = None
        for i in range(60):  # Max 2 minutes of polling
            await asyncio.sleep(2)
            poll_result = await tools.check_proof(project_id=project_id)

            print(f"Poll {i + 1}: {poll_result.status} ({poll_result.percent_complete}%)")

            if poll_result.status in ("proved", "failed", "error", "counterexample"):
                final_result = poll_result
                break

        assert final_result is not None, "Polling timed out"
        assert final_result.status == "proved", f"Expected proved, got {final_result.status}"
        assert final_result.code is not None
        assert final_result.percent_complete == 100


class TestProveFileSync:
    """Test prove_file() with wait=True (synchronous)."""

    @pytest.mark.timeout(180)
    async def test_prove_file_sync(self, tools, lean_file: str, tmp_path) -> None:
        """Test proving a file synchronously."""
        output_path = str(tmp_path / "solved.lean")

        result = await tools.prove_file(
            file_path=lean_file,
            output_path=output_path,
            wait=True,
        )

        print(f"\nStatus: {result.status}")
        print(f"Sorries: {result.sorries_filled}/{result.sorries_total}")
        print(f"Output: {result.output_path}")
        print(f"Message: {result.message}")

        assert result.status in ("proved", "partial"), f"Unexpected status: {result.status}"
        assert result.sorries_total == 2
        assert result.sorries_filled > 0
        assert result.output_path is not None

        # Verify output file exists and has content
        assert os.path.exists(result.output_path)
        with open(result.output_path) as f:
            solved_content = f.read()
        print(f"\nSolved content:\n{solved_content}")


class TestProveFileAsync:
    """Test prove_file() with wait=False (asynchronous polling)."""

    @pytest.mark.timeout(180)
    async def test_prove_file_async_flow(self, tools, lean_file: str, tmp_path) -> None:
        """Test the full async flow for file proving."""
        import asyncio

        # Submit
        submit_result = await tools.prove_file(file_path=lean_file, wait=False)

        print(f"\nSubmit status: {submit_result.status}")
        print(f"Project ID: {submit_result.project_id}")
        print(f"Sorries total: {submit_result.sorries_total}")

        assert submit_result.status == "submitted"
        assert submit_result.project_id is not None
        assert submit_result.sorries_total == 2

        project_id = submit_result.project_id
        output_path = str(tmp_path / "solved.lean")

        # Poll until complete
        final_result = None
        for i in range(60):
            await asyncio.sleep(2)
            poll_result = await tools.check_prove_file(
                project_id=project_id,
                output_path=output_path,
            )

            print(f"Poll {i + 1}: {poll_result.status} ({poll_result.percent_complete}%)")

            if poll_result.status in ("proved", "partial", "failed", "error"):
                final_result = poll_result
                break

        assert final_result is not None, "Polling timed out"
        assert final_result.status in ("proved", "partial")
        print(f"\nFinal: {final_result.sorries_filled}/{final_result.sorries_total} filled")


class TestFormalize:
    """Test formalize() function."""

    @pytest.mark.timeout(180)
    async def test_formalize_simple(self, tools) -> None:
        """Test formalizing a simple natural language statement."""
        result = await tools.formalize(
            description="The sum of two even numbers is even",
            prove=False,
        )

        print(f"\nStatus: {result.status}")
        print(f"Message: {result.message}")
        if result.lean_code:
            print(f"Lean code:\n{result.lean_code}")

        assert result.status in ("formalized", "proved"), f"Unexpected: {result.status}"
        assert result.lean_code is not None
        assert "even" in result.lean_code.lower() or "theorem" in result.lean_code.lower()

    @pytest.mark.timeout(180)
    async def test_formalize_and_prove(self, tools) -> None:
        """Test formalizing and proving a statement."""
        result = await tools.formalize(
            description="Addition of natural numbers is commutative: a + b = b + a",
            prove=True,
        )

        print(f"\nStatus: {result.status}")
        print(f"Message: {result.message}")
        if result.lean_code:
            print(f"Lean code:\n{result.lean_code}")

        # May or may not be proved depending on complexity
        assert result.status in ("formalized", "proved")
        assert result.lean_code is not None
