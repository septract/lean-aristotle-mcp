"""Unit tests for helper functions and models."""

from pathlib import Path

import pytest

from aristotle_mcp.models import FormalizeResult, ProveFileResult, ProveResult
from aristotle_mcp.tools import (
    _count_sorries,
    _find_unique_path,
    _map_api_status,
)


class TestCountSorries:
    """Tests for _count_sorries helper."""

    def test_no_sorries(self) -> None:
        """Text with no sorry statements."""
        assert _count_sorries("theorem foo : True := trivial") == 0

    def test_single_sorry(self) -> None:
        """Text with one sorry."""
        assert _count_sorries("theorem foo : True := by sorry") == 1

    def test_multiple_sorries(self) -> None:
        """Text with multiple sorry statements."""
        code = """
        theorem a : True := by sorry
        theorem b : False := by sorry
        theorem c : 1 = 1 := by sorry
        """
        assert _count_sorries(code) == 3

    def test_sorry_word_boundary(self) -> None:
        """Should not match 'sorry' as part of another word."""
        # "sorryExample" should not count
        assert _count_sorries("def sorryExample := 1") == 0
        # "notsorry" should not count
        assert _count_sorries("-- notsorry comment") == 0
        # But "sorry" alone should count
        assert _count_sorries("-- sorry") == 1

    def test_sorry_in_comment(self) -> None:
        """Sorry in comments still counts (matches real behavior)."""
        assert _count_sorries("-- TODO: sorry") == 1


class TestFindUniquePath:
    """Tests for _find_unique_path helper."""

    def test_path_does_not_exist(self, tmp_path: Path) -> None:
        """Returns original path if it doesn't exist."""
        path = str(tmp_path / "nonexistent.lean")
        assert _find_unique_path(path) == path

    def test_path_exists_finds_unique(self, tmp_path: Path) -> None:
        """Finds unique path by adding number suffix."""
        # Create the original file
        original = tmp_path / "test.lean"
        original.write_text("-- original")

        result = _find_unique_path(str(original))
        expected = str(tmp_path / "test.1.lean")
        assert result == expected

    def test_multiple_existing_files(self, tmp_path: Path) -> None:
        """Skips existing numbered files."""
        # Create original and first few numbered versions
        (tmp_path / "test.lean").write_text("-- original")
        (tmp_path / "test.1.lean").write_text("-- v1")
        (tmp_path / "test.2.lean").write_text("-- v2")

        result = _find_unique_path(str(tmp_path / "test.lean"))
        expected = str(tmp_path / "test.3.lean")
        assert result == expected

    def test_max_attempts_exceeded(self, tmp_path: Path) -> None:
        """Raises RuntimeError if max_attempts exceeded."""
        original = tmp_path / "test.lean"
        original.write_text("-- original")

        # Create files for attempts 1-3
        for i in range(1, 4):
            (tmp_path / f"test.{i}.lean").write_text(f"-- v{i}")

        with pytest.raises(RuntimeError, match="Could not find unique path"):
            _find_unique_path(str(original), max_attempts=3)


class TestMapApiStatus:
    """Tests for _map_api_status helper."""

    def test_complete(self) -> None:
        """COMPLETE maps to complete."""
        status, message = _map_api_status("COMPLETE", 100)
        assert status == "complete"
        assert "completed" in message.lower()

    def test_queued(self) -> None:
        """QUEUED maps to queued."""
        status, message = _map_api_status("QUEUED", 0)
        assert status == "queued"
        assert "queued" in message.lower()

    def test_not_started(self) -> None:
        """NOT_STARTED maps to queued."""
        status, message = _map_api_status("NOT_STARTED", 0)
        assert status == "queued"

    def test_in_progress(self) -> None:
        """IN_PROGRESS maps to in_progress with percent."""
        status, message = _map_api_status("IN_PROGRESS", 42)
        assert status == "in_progress"
        assert "42%" in message

    def test_pending_retry(self) -> None:
        """PENDING_RETRY maps to in_progress."""
        status, message = _map_api_status("PENDING_RETRY", 50)
        assert status == "in_progress"
        assert "retry" in message.lower()

    def test_failed(self) -> None:
        """FAILED maps to failed."""
        status, message = _map_api_status("FAILED", 0)
        assert status == "failed"
        assert "failed" in message.lower()

    def test_unknown_status(self) -> None:
        """Unknown status maps to in_progress."""
        status, message = _map_api_status("UNKNOWN_STATUS", 25)
        assert status == "in_progress"
        assert "UNKNOWN_STATUS" in message

    def test_none_percent_complete(self) -> None:
        """Handles None percent_complete gracefully."""
        status, message = _map_api_status("IN_PROGRESS", None)
        assert status == "in_progress"
        assert "0%" in message


class TestProveResultToDict:
    """Tests for ProveResult.to_dict()."""

    def test_minimal(self) -> None:
        """Minimal result with just status and message."""
        result = ProveResult(status="proved", message="Success")
        d = result.to_dict()
        assert d == {"status": "proved", "message": "Success"}

    def test_with_code(self) -> None:
        """Result with code included."""
        result = ProveResult(status="proved", code="theorem x := y", message="Done")
        d = result.to_dict()
        assert d["code"] == "theorem x := y"

    def test_with_counterexample(self) -> None:
        """Result with counterexample."""
        result = ProveResult(
            status="counterexample",
            counterexample="n=0 is a counterexample",
            message="False",
        )
        d = result.to_dict()
        assert d["counterexample"] == "n=0 is a counterexample"

    def test_with_project_id(self) -> None:
        """Result with project_id."""
        result = ProveResult(status="submitted", project_id="abc-123", message="Submitted")
        d = result.to_dict()
        assert d["project_id"] == "abc-123"

    def test_with_percent_complete(self) -> None:
        """Result with percent_complete."""
        result = ProveResult(status="in_progress", percent_complete=50, message="Working")
        d = result.to_dict()
        assert d["percent_complete"] == 50

    def test_none_values_excluded(self) -> None:
        """None values are not included in dict."""
        result = ProveResult(status="proved", code=None, message="Done")
        d = result.to_dict()
        assert "code" not in d


class TestProveFileResultToDict:
    """Tests for ProveFileResult.to_dict()."""

    def test_minimal(self) -> None:
        """Minimal result."""
        result = ProveFileResult(status="proved", message="Done")
        d = result.to_dict()
        assert d["status"] == "proved"
        assert d["sorries_filled"] == 0
        assert d["sorries_total"] == 0

    def test_with_counts(self) -> None:
        """Result with sorry counts."""
        result = ProveFileResult(
            status="partial",
            sorries_filled=3,
            sorries_total=5,
            message="Partial",
        )
        d = result.to_dict()
        assert d["sorries_filled"] == 3
        assert d["sorries_total"] == 5

    def test_with_output_path(self) -> None:
        """Result with output_path."""
        result = ProveFileResult(
            status="proved",
            output_path="/tmp/out.lean",
            message="Done",
        )
        d = result.to_dict()
        assert d["output_path"] == "/tmp/out.lean"


class TestFormalizeResultToDict:
    """Tests for FormalizeResult.to_dict()."""

    def test_minimal(self) -> None:
        """Minimal result."""
        result = FormalizeResult(status="formalized", message="Done")
        d = result.to_dict()
        assert d == {"status": "formalized", "message": "Done"}

    def test_with_lean_code(self) -> None:
        """Result with lean_code."""
        result = FormalizeResult(
            status="formalized",
            lean_code="theorem x : True := trivial",
            message="Formalized",
        )
        d = result.to_dict()
        assert d["lean_code"] == "theorem x : True := trivial"
