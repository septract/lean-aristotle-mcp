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
def file_with_partial_name(tmp_path: Path) -> Path:
    """Create a file with 'partial' in name (triggers partial success in mock)."""
    content = "theorem t : True := by sorry"
    path = tmp_path / "partial_test.lean"
    path.write_text(content)
    return path


@pytest.fixture
def simple_lean_file(tmp_path: Path) -> Path:
    """Create a simple Lean file."""
    content = "theorem proved : True := trivial"
    path = tmp_path / "simple.lean"
    path.write_text(content)
    return path


class TestProveEdgeCases:
    """Edge case tests for prove()."""

    async def test_already_proved_code(self) -> None:
        """Code without sorry is accepted (API handles validation)."""
        code = "theorem already_proved : True := trivial"
        result = await prove(code)

        # Mock mode returns proved for any valid code
        assert result.status == "proved"

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

    async def test_simple_file(self, simple_lean_file: Path) -> None:
        """Simple Lean file is accepted (API handles validation)."""
        result = await prove_file(str(simple_lean_file))

        # Mock mode returns proved for files without special keywords
        assert result.status == "proved"

    async def test_partial_success(
        self, file_with_partial_name: Path, tmp_path: Path
    ) -> None:
        """File with 'partial' in name triggers partial success in mock."""
        output = tmp_path / "output.lean"
        result = await prove_file(
            str(file_with_partial_name),
            output_path=str(output),
        )

        assert result.status == "partial"
        assert "could not" in result.message.lower()

    async def test_empty_file(self, tmp_path: Path) -> None:
        """Empty file is accepted (API handles validation)."""
        empty = tmp_path / "empty.lean"
        empty.write_text("")

        result = await prove_file(str(empty))

        # Mock mode returns proved for any file without special keywords
        assert result.status == "proved"

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


class TestInputSizeLimits:
    """Tests for input size validation."""

    async def test_prove_code_size_limit(self) -> None:
        """Code exceeding size limit returns error."""
        from aristotle_mcp.tools import _MAX_CODE_SIZE

        # Create code that exceeds the limit
        line = "theorem t : True := by sorry\n"
        huge_code = line * (_MAX_CODE_SIZE // len(line) + 100)
        assert len(huge_code) > _MAX_CODE_SIZE

        result = await prove(huge_code)

        assert result.status == "error"
        assert "size" in result.message.lower() or "exceeds" in result.message.lower()

    async def test_prove_file_size_limit(self, tmp_path: Path) -> None:
        """File exceeding size limit returns error."""
        from aristotle_mcp.tools import _MAX_FILE_SIZE

        # Create a file that exceeds the limit
        huge_file = tmp_path / "huge.lean"
        # Write in chunks to avoid memory issues
        with open(huge_file, "w") as f:
            chunk = "theorem t : True := by sorry\n" * 10000
            bytes_written = 0
            while bytes_written < _MAX_FILE_SIZE + 1000:
                f.write(chunk)
                bytes_written += len(chunk)

        result = await prove_file(str(huge_file))

        assert result.status == "error"
        assert "size" in result.message.lower() or "exceeds" in result.message.lower()

    async def test_formalize_description_size_limit(self) -> None:
        """Description exceeding size limit returns error."""
        from aristotle_mcp.tools import _MAX_DESCRIPTION_SIZE

        # Create description that exceeds the limit
        huge_description = "Prove that " * (_MAX_DESCRIPTION_SIZE // 10 + 1)
        assert len(huge_description) > _MAX_DESCRIPTION_SIZE

        result = await formalize(huge_description)

        assert result.status == "error"
        assert "size" in result.message.lower() or "exceeds" in result.message.lower()

    async def test_prove_within_size_limit(self) -> None:
        """Code within size limit is accepted."""
        code = "theorem t : True := by sorry"
        result = await prove(code)

        # Should not fail due to size
        assert result.status != "error" or "size" not in result.message.lower()

    async def test_formalize_within_size_limit(self) -> None:
        """Description within size limit is accepted."""
        description = "The sum of two even numbers is even"
        result = await formalize(description)

        # Should not fail due to size
        assert result.status != "error" or "size" not in result.message.lower()
