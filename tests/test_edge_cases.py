"""Edge case tests for Aristotle MCP tools."""

import os
from pathlib import Path

import pytest

# Force mock mode for these tests
os.environ["ARISTOTLE_MOCK"] = "true"

from aristotle_mcp.tools import (
    check_proof,
    check_prove_file,
    formalize,
    prove,
    prove_file,
)

FIXTURES_DIR = Path(__file__).parent / "fixtures"


@pytest.fixture
def file_with_many_sorries(tmp_path: Path) -> Path:
    """Create a file with more than 5 sorries (triggers partial success in mock)."""
    content = "\n".join(
        [f"theorem t{i} : True := by sorry" for i in range(7)]
    )
    path = tmp_path / "many_sorries.lean"
    path.write_text(content)
    return path


@pytest.fixture
def file_without_sorries(tmp_path: Path) -> Path:
    """Create a file with no sorry statements."""
    content = "theorem proved : True := trivial"
    path = tmp_path / "no_sorries.lean"
    path.write_text(content)
    return path


class TestProveEdgeCases:
    """Edge case tests for prove()."""

    async def test_no_sorry_statements(self) -> None:
        """Code with no sorry should return error."""
        code = "theorem already_proved : True := trivial"
        result = await prove(code)

        assert result.status == "error"
        assert "sorry" in result.message.lower()

    async def test_timeout_failure(self) -> None:
        """Code that triggers timeout/failure in mock."""
        code = "theorem hard_theorem : 1 = 1 := by sorry"
        result = await prove(code)

        assert result.status == "failed"
        assert "time" in result.message.lower() or "limit" in result.message.lower()

    async def test_multiple_sorries(self) -> None:
        """Code with multiple sorry statements."""
        code = """
        theorem a : True := by sorry
        theorem b : True := by sorry
        theorem c : True := by sorry
        """
        result = await prove(code)

        assert result.status == "proved"
        assert result.code is not None
        # All sorries should be filled
        assert "sorry" not in result.code or "filled by Aristotle" in result.code


class TestCheckProofEdgeCases:
    """Edge case tests for check_proof()."""

    async def test_unknown_project_id(self) -> None:
        """Unknown project_id should return error."""
        result = await check_proof("nonexistent-project-id")

        assert result.status == "error"
        assert "unknown" in result.message.lower()

    async def test_invalid_project_id_format(self) -> None:
        """Invalid project_id format should return error."""
        result = await check_proof("")

        assert result.status == "error"


class TestProveFileEdgeCases:
    """Edge case tests for prove_file()."""

    async def test_no_sorries_in_file(self, file_without_sorries: Path) -> None:
        """File with no sorry statements should return error."""
        result = await prove_file(str(file_without_sorries))

        assert result.status == "error"
        assert "sorry" in result.message.lower()

    async def test_partial_success(
        self, file_with_many_sorries: Path, tmp_path: Path
    ) -> None:
        """File with >5 sorries triggers partial success in mock."""
        output = tmp_path / "output.lean"
        result = await prove_file(
            str(file_with_many_sorries),
            output_path=str(output),
        )

        assert result.status == "partial"
        assert result.sorries_total == 7
        assert result.sorries_filled == 5  # Mock fills total - 2 for >5 sorries
        assert result.sorries_filled < result.sorries_total

    async def test_empty_file(self, tmp_path: Path) -> None:
        """Empty file should return error (no sorries)."""
        empty = tmp_path / "empty.lean"
        empty.write_text("")

        result = await prove_file(str(empty))

        assert result.status == "error"
        assert "sorry" in result.message.lower()

    async def test_custom_output_path(self, tmp_path: Path) -> None:
        """Verify custom output path is used."""
        # Create input file
        input_file = tmp_path / "input.lean"
        input_file.write_text("theorem x : True := by sorry")

        # Specify custom output
        output_file = tmp_path / "custom_output.lean"

        result = await prove_file(str(input_file), output_path=str(output_file))

        assert result.status == "proved"
        assert result.output_path == str(output_file)


class TestCheckProveFileEdgeCases:
    """Edge case tests for check_prove_file()."""

    async def test_unknown_project_id(self) -> None:
        """Unknown project_id should return error."""
        result = await check_prove_file("nonexistent-file-project-id")

        assert result.status == "error"
        assert "unknown" in result.message.lower()


class TestFormalizeEdgeCases:
    """Edge case tests for formalize()."""

    async def test_context_file_not_found(self) -> None:
        """Non-existent context file should return error (in non-mock mode).

        Note: Mock mode doesn't validate context file existence, so this test
        verifies the mock behavior. Real API tests cover actual validation.
        """
        # In mock mode, context file is not validated for existence
        result = await formalize(
            "Some theorem",
            context_file="/nonexistent/context.lean",
        )
        # Mock mode accepts any context file path
        assert result.status == "formalized"

    async def test_prime_formalization(self) -> None:
        """Test prime-related formalization (mock keyword detection)."""
        result = await formalize("7 is a prime number")

        assert result.status == "formalized"
        assert result.lean_code is not None
        assert "prime" in result.lean_code.lower()

    async def test_commutative_formalization(self) -> None:
        """Test commutativity formalization (mock keyword detection)."""
        result = await formalize("addition is commutative")

        assert result.status == "formalized"
        assert result.lean_code is not None
        assert "comm" in result.lean_code.lower()

    async def test_generic_formalization(self) -> None:
        """Test generic formalization when no keywords match."""
        result = await formalize("something random that doesn't match keywords")

        assert result.status == "formalized"
        assert result.lean_code is not None
        assert "theorem" in result.lean_code.lower()

    async def test_formalize_with_prove_partial(self) -> None:
        """Formalize with prove=True but mock leaves sorry."""
        # Generic descriptions leave sorry even with prove=True in some cases
        result = await formalize("generic statement", prove=True)

        # Should succeed (mock replaces sorry with trivial for generic)
        assert result.status == "proved"
