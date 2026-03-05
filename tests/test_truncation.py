"""Tests for response truncation (verbose parameter and _truncate_code)."""

import os

os.environ["ARISTOTLE_MOCK"] = "true"

from aristotle_mcp.models import (
    _DEFAULT_MAX_CHARS,
    FormalizeResult,
    ProveFileResult,
    ProveResult,
    _truncate_code,
)
from aristotle_mcp.server import (
    check_formalize_tool,
    check_proof_tool,
    formalize_tool,
    prove_tool,
)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_long_code(num_lines: int = 200, line_len: int = 60) -> str:
    """Generate code that exceeds _DEFAULT_MAX_CHARS."""
    return "\n".join(f"-- line {i}: {'x' * line_len}" for i in range(num_lines))


def _make_short_code() -> str:
    """Generate code well under _DEFAULT_MAX_CHARS."""
    return "import Mathlib.Tactic\n\ntheorem add_zero (n : Nat) : n + 0 = n := by simp"


# ---------------------------------------------------------------------------
# _truncate_code helper
# ---------------------------------------------------------------------------

class TestTruncateCode:
    """Tests for the _truncate_code helper function."""

    def test_under_limit_unchanged(self) -> None:
        """Code under the limit is returned as-is."""
        code = _make_short_code()
        preview, lines, nbytes = _truncate_code(code)
        assert preview == code
        assert lines == code.count("\n") + 1
        assert nbytes == len(code.encode("utf-8"))

    def test_over_limit_truncated(self) -> None:
        """Code over the limit is truncated at a line boundary."""
        code = _make_long_code()
        assert len(code) > _DEFAULT_MAX_CHARS
        preview, lines, nbytes = _truncate_code(code)
        assert len(preview) <= _DEFAULT_MAX_CHARS
        assert preview == preview.rstrip("\n")  # no trailing newline in preview
        assert not preview.endswith("\n")
        # Preview is a proper prefix of lines
        assert code.startswith(preview)
        # Metadata reflects the full code
        assert lines == code.count("\n") + 1
        assert nbytes == len(code.encode("utf-8"))

    def test_empty_string(self) -> None:
        """Empty string passes through unchanged."""
        preview, lines, nbytes = _truncate_code("")
        assert preview == ""
        assert lines == 0
        assert nbytes == 0

    def test_single_long_line_no_newlines(self) -> None:
        """A single line longer than max_chars: hard-truncated at max_chars."""
        code = "x" * (_DEFAULT_MAX_CHARS + 500)
        preview, lines, nbytes = _truncate_code(code)
        assert len(preview) == _DEFAULT_MAX_CHARS
        assert preview == code[:_DEFAULT_MAX_CHARS]
        assert lines == 1

    def test_single_long_line_with_trailing_newline(self) -> None:
        """A long first line followed by more: hard-truncated at max_chars."""
        first_line = "x" * (_DEFAULT_MAX_CHARS + 100)
        code = first_line + "\nshort second line"
        preview, lines, nbytes = _truncate_code(code)
        # No newline before the limit, so hard-truncate at max_chars
        assert len(preview) == _DEFAULT_MAX_CHARS
        assert preview == code[:_DEFAULT_MAX_CHARS]
        assert lines == 2

    def test_exactly_at_limit(self) -> None:
        """Code exactly at the char limit is not truncated."""
        # Build code that is exactly _DEFAULT_MAX_CHARS
        base = "a" * (_DEFAULT_MAX_CHARS - 1) + "\n"
        code = base[:_DEFAULT_MAX_CHARS]
        assert len(code) == _DEFAULT_MAX_CHARS
        preview, _, _ = _truncate_code(code)
        assert preview == code

    def test_custom_max_chars(self) -> None:
        """Custom max_chars parameter is respected."""
        code = "line1\nline2\nline3\nline4\nline5"
        preview, lines, nbytes = _truncate_code(code, max_chars=12)
        # "line1\nline2\n" is 12 chars; rfind("\n", 0, 12) finds position 11
        assert len(preview) <= 12
        assert lines == 5
        assert nbytes == len(code.encode("utf-8"))

    def test_line_count_accuracy(self) -> None:
        """Line count reflects the full code, not the preview."""
        code = _make_long_code(num_lines=300)
        _, lines, _ = _truncate_code(code)
        assert lines == 300

    def test_byte_count_accuracy(self) -> None:
        """Byte count reflects the full code including multi-byte chars."""
        code = "theorem café : True := trivial\n" * 200
        _, _, nbytes = _truncate_code(code)
        assert nbytes == len(code.encode("utf-8"))
        # 'é' is 2 bytes in UTF-8, so bytes > chars
        assert nbytes > len(code)

    def test_truncation_at_line_boundary(self) -> None:
        """When newlines exist before the limit, preview ends at a line boundary."""
        code = _make_long_code()
        preview, _, _ = _truncate_code(code)
        if preview != code:
            # Lines are short enough that we always find a newline before max_chars
            assert code[len(preview)] == "\n"

    def test_hard_truncation_when_no_newline_before_limit(self) -> None:
        """When no newline exists before max_chars, hard-truncate at max_chars."""
        # Build code where the first newline is after the limit
        code = "x" * (_DEFAULT_MAX_CHARS + 50) + "\nafter"
        preview, _, _ = _truncate_code(code)
        assert len(preview) == _DEFAULT_MAX_CHARS


# ---------------------------------------------------------------------------
# ProveResult.to_dict(verbose=...)
# ---------------------------------------------------------------------------

class TestProveResultTruncation:
    """Tests for ProveResult truncation via to_dict(verbose=...)."""

    def test_short_code_not_truncated(self) -> None:
        """Short code returns full 'code' field even with verbose=False."""
        result = ProveResult(status="proved", code=_make_short_code(), message="Done")
        d = result.to_dict(verbose=False)
        assert "code" in d
        assert d["code"] == _make_short_code()
        assert "truncated" not in d
        assert "code_preview" not in d

    def test_long_code_truncated_by_default(self) -> None:
        """Long code is truncated when verbose=False (default)."""
        long_code = _make_long_code()
        result = ProveResult(status="proved", code=long_code, message="Done")
        d = result.to_dict()  # verbose=False is default
        assert "code" not in d
        assert "code_preview" in d
        assert isinstance(d["code_preview"], str)
        assert len(str(d["code_preview"])) < len(long_code)
        assert d["code_lines"] == long_code.count("\n") + 1
        assert d["code_bytes"] == len(long_code.encode("utf-8"))
        assert d["truncated"] is True
        assert "hint" in d
        assert "verbose=True" in str(d["hint"])
        assert "prove_file" in str(d["hint"])  # file_hint for prove

    def test_long_code_verbose_returns_full(self) -> None:
        """Long code with verbose=True returns full 'code' field."""
        long_code = _make_long_code()
        result = ProveResult(status="proved", code=long_code, message="Done")
        d = result.to_dict(verbose=True)
        assert d["code"] == long_code
        assert "truncated" not in d
        assert "code_preview" not in d

    def test_none_code_unaffected(self) -> None:
        """None code is not affected by verbose setting."""
        result = ProveResult(status="failed", message="Failed")
        for verbose in (True, False):
            d = result.to_dict(verbose=verbose)
            assert "code" not in d
            assert "code_preview" not in d
            assert "truncated" not in d

    def test_counterexample_truncated_when_large(self) -> None:
        """Large counterexample is truncated with verbose=False."""
        large_cx = _make_long_code(num_lines=200)
        result = ProveResult(
            status="counterexample", counterexample=large_cx, message="False"
        )
        d = result.to_dict(verbose=False)
        assert "counterexample" not in d
        assert "counterexample_preview" in d
        assert d["truncated"] is True

    def test_counterexample_not_truncated_verbose(self) -> None:
        """Large counterexample returned in full with verbose=True."""
        large_cx = _make_long_code(num_lines=200)
        result = ProveResult(
            status="counterexample", counterexample=large_cx, message="False"
        )
        d = result.to_dict(verbose=True)
        assert d["counterexample"] == large_cx
        assert "truncated" not in d

    def test_small_counterexample_not_truncated(self) -> None:
        """Small counterexample passes through regardless of verbose."""
        result = ProveResult(
            status="counterexample", counterexample="n=0", message="False"
        )
        d = result.to_dict(verbose=False)
        assert d["counterexample"] == "n=0"
        assert "truncated" not in d

    def test_other_fields_always_pass_through(self) -> None:
        """status, message, project_id, percent_complete are never truncated."""
        long_code = _make_long_code()
        result = ProveResult(
            status="proved",
            code=long_code,
            project_id="abc-123",
            percent_complete=100,
            message="All done",
        )
        d = result.to_dict(verbose=False)
        assert d["status"] == "proved"
        assert d["message"] == "All done"
        assert d["project_id"] == "abc-123"
        assert d["percent_complete"] == 100

    def test_both_code_and_counterexample_large(self) -> None:
        """When both code and counterexample are large, hint mentions both."""
        long_code = _make_long_code()
        long_cx = _make_long_code(num_lines=200, line_len=40)
        result = ProveResult(
            status="counterexample",
            code=long_code,
            counterexample=long_cx,
            message="Found",
        )
        d = result.to_dict(verbose=False)
        assert d["truncated"] is True
        assert "code_preview" in d
        assert "counterexample_preview" in d
        # Hint should mention both fields
        hint = str(d["hint"])
        assert "code" in hint
        assert "counterexample" in hint
        assert "prove_file" in hint  # file_hint for code


# ---------------------------------------------------------------------------
# FormalizeResult.to_dict(verbose=...)
# ---------------------------------------------------------------------------

class TestFormalizeResultTruncation:
    """Tests for FormalizeResult truncation via to_dict(verbose=...)."""

    def test_short_lean_code_not_truncated(self) -> None:
        """Short lean_code returns full field with verbose=False."""
        result = FormalizeResult(
            status="formalized", lean_code=_make_short_code(), message="Done"
        )
        d = result.to_dict(verbose=False)
        assert "lean_code" in d
        assert d["lean_code"] == _make_short_code()
        assert "truncated" not in d

    def test_long_lean_code_truncated_by_default(self) -> None:
        """Long lean_code is truncated when verbose=False."""
        long_code = _make_long_code()
        result = FormalizeResult(status="formalized", lean_code=long_code, message="Done")
        d = result.to_dict()
        assert "lean_code" not in d
        assert "lean_code_preview" in d
        assert d["lean_code_lines"] == long_code.count("\n") + 1
        assert d["lean_code_bytes"] == len(long_code.encode("utf-8"))
        assert d["truncated"] is True
        assert "verbose=True" in str(d["hint"])
        # No prove_file hint for formalize
        assert "prove_file" not in str(d["hint"])

    def test_long_lean_code_verbose_returns_full(self) -> None:
        """Long lean_code with verbose=True returns full field."""
        long_code = _make_long_code()
        result = FormalizeResult(status="formalized", lean_code=long_code, message="Done")
        d = result.to_dict(verbose=True)
        assert d["lean_code"] == long_code
        assert "truncated" not in d

    def test_none_lean_code_unaffected(self) -> None:
        """None lean_code is not affected by verbose setting."""
        result = FormalizeResult(status="failed", message="Failed")
        for verbose in (True, False):
            d = result.to_dict(verbose=verbose)
            assert "lean_code" not in d
            assert "lean_code_preview" not in d

    def test_other_fields_always_pass_through(self) -> None:
        """status, message, project_id, percent_complete are never truncated."""
        long_code = _make_long_code()
        result = FormalizeResult(
            status="formalized",
            lean_code=long_code,
            project_id="xyz-789",
            percent_complete=100,
            message="Formalized",
        )
        d = result.to_dict(verbose=False)
        assert d["status"] == "formalized"
        assert d["message"] == "Formalized"
        assert d["project_id"] == "xyz-789"
        assert d["percent_complete"] == 100


# ---------------------------------------------------------------------------
# ProveFileResult (no truncation, no verbose)
# ---------------------------------------------------------------------------

class TestProveFileResultNoTruncation:
    """ProveFileResult has no verbose param — it returns paths, not code."""

    def test_no_verbose_parameter(self) -> None:
        """ProveFileResult.to_dict() does not accept verbose."""
        result = ProveFileResult(
            status="proved", output_path="/tmp/out.lean", message="Done"
        )
        d = result.to_dict()
        assert d["status"] == "proved"
        assert d["output_path"] == "/tmp/out.lean"
        assert "truncated" not in d


# ---------------------------------------------------------------------------
# Integration tests (through server tool wrappers, mock mode)
# ---------------------------------------------------------------------------

class TestProveToolIntegration:
    """End-to-end tests for prove tool with verbose parameter."""

    async def test_prove_default_returns_code(self) -> None:
        """prove with short code returns full code (under limit)."""
        code = "theorem one_plus_one : 1 + 1 = 2 := by sorry"
        d = await prove_tool(code=code)
        # Mock returns the input code with a comment appended — should be short
        assert d["status"] == "proved"
        assert "code" in d
        assert "truncated" not in d

    async def test_prove_verbose_true(self) -> None:
        """prove with verbose=True always returns full code."""
        code = "theorem one_plus_one : 1 + 1 = 2 := by sorry"
        d = await prove_tool(code=code, verbose=True)
        assert d["status"] == "proved"
        assert "code" in d
        assert "truncated" not in d

    async def test_prove_async_check_verbose(self) -> None:
        """check_proof passes verbose through correctly."""
        code = "theorem async_test : 1 + 1 = 2 := by sorry"
        submit = await prove_tool(code=code, wait=False)
        assert submit["status"] == "submitted"
        project_id = str(submit["project_id"])

        # Poll until proved
        for _ in range(5):
            d = await check_proof_tool(project_id=project_id, verbose=True)
            if d["status"] == "proved":
                break
        assert d["status"] == "proved"
        assert "code" in d
        assert "truncated" not in d


class TestFormalizeToolIntegration:
    """End-to-end tests for formalize tool with verbose parameter."""

    async def test_formalize_default(self) -> None:
        """formalize with default verbose returns lean_code (short mock output)."""
        d = await formalize_tool(description="The sum of two even numbers is even")
        assert d["status"] == "formalized"
        assert "lean_code" in d
        assert "truncated" not in d

    async def test_formalize_verbose_true(self) -> None:
        """formalize with verbose=True returns full lean_code."""
        d = await formalize_tool(
            description="The sum of two even numbers is even", verbose=True
        )
        assert d["status"] == "formalized"
        assert "lean_code" in d
        assert "truncated" not in d

    async def test_formalize_async_check_verbose(self) -> None:
        """check_formalize passes verbose through correctly."""
        submit = await formalize_tool(
            description="addition is commutative", wait=False
        )
        assert submit["status"] == "submitted"
        project_id = str(submit["project_id"])

        # Poll until complete
        for _ in range(5):
            d = await check_formalize_tool(project_id=project_id, verbose=True)
            if d["status"] in ("formalized", "proved"):
                break
        assert d["status"] in ("formalized", "proved")
        assert "lean_code" in d
        assert "truncated" not in d
