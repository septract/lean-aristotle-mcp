"""Result models for the Aristotle MCP server."""

from __future__ import annotations

from dataclasses import dataclass

# Type for JSON-serializable result dictionaries
ResultValue = str | int | bool | None
ResultDict = dict[str, ResultValue]

# Default character limit for code fields in non-verbose responses.
# At ~4 chars/token, 4000 chars ≈ 1000 tokens — well under Claude Code's
# 10K-token warning threshold for MCP responses.
_DEFAULT_MAX_CHARS = 4000


def _truncate_code(code: str, max_chars: int = _DEFAULT_MAX_CHARS) -> tuple[str, int, int]:
    """Truncate code at a line boundary at or before max_chars.

    Returns (preview, total_lines, total_bytes).
    If the code is within the limit, preview == code.
    When no line boundary exists before the limit, hard-truncates at max_chars.
    """
    total_lines = code.count("\n") + (1 if code else 0)
    total_bytes = len(code.encode("utf-8"))
    if len(code) <= max_chars:
        return code, total_lines, total_bytes
    # Prefer a line boundary; fall back to hard truncation at max_chars
    cut = code.rfind("\n", 0, max_chars)
    preview = code[:max_chars] if cut == -1 else code[:cut]
    return preview, total_lines, total_bytes


def _code_field(
    value: str, name: str, *, verbose: bool
) -> tuple[ResultDict, bool]:
    """Build dict entries for a code field, truncating if needed.

    Returns (fields_dict, was_truncated).
    When verbose=True or the value is within the limit, returns ({name: value}, False).
    Otherwise returns ({name_preview, name_lines, name_bytes}, True).
    """
    preview, total_lines, total_bytes = _truncate_code(value)
    if verbose or preview == value:
        return {name: value}, False
    return {
        f"{name}_preview": preview,
        f"{name}_lines": total_lines,
        f"{name}_bytes": total_bytes,
    }, True


@dataclass
class ProveResult:
    """Result from a prove operation."""

    status: str  # proved | counterexample | failed | error | submitted | in_progress | queued
    code: str | None = None
    counterexample: str | None = None
    project_id: str | None = None
    percent_complete: int | None = None
    message: str = ""

    def to_dict(self, *, verbose: bool = False) -> ResultDict:
        """Convert to dictionary for JSON serialization.

        When verbose=False (the default), large code fields are truncated to a
        preview to keep MCP responses token-efficient. Use verbose=True to get
        the full output.
        """
        result: ResultDict = {"status": self.status, "message": self.message}
        truncated_fields: list[str] = []
        if self.code is not None:
            fields, was_truncated = _code_field(self.code, "code", verbose=verbose)
            result.update(fields)
            if was_truncated:
                truncated_fields.append("code")
        if self.counterexample is not None:
            fields, was_truncated = _code_field(
                self.counterexample, "counterexample", verbose=verbose
            )
            result.update(fields)
            if was_truncated:
                truncated_fields.append("counterexample")
        if truncated_fields:
            result["truncated"] = True
            names = " and ".join(truncated_fields)
            hint = f"Call again with verbose=True to get the full {names}."
            if "code" in truncated_fields:
                hint += " Or use prove_file to write directly to a file."
            result["hint"] = hint
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
    project_id: str | None = None
    percent_complete: int | None = None
    message: str = ""

    def to_dict(self) -> ResultDict:
        """Convert to dictionary for JSON serialization."""
        result: ResultDict = {
            "status": self.status,
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

    status: str  # formalized | proved | failed | error | submitted | in_progress | queued
    lean_code: str | None = None
    project_id: str | None = None
    percent_complete: int | None = None
    message: str = ""

    def to_dict(self, *, verbose: bool = False) -> ResultDict:
        """Convert to dictionary for JSON serialization.

        When verbose=False (the default), large lean_code fields are truncated
        to a preview. Use verbose=True to get the full output.
        """
        result: ResultDict = {"status": self.status, "message": self.message}
        if self.lean_code is not None:
            fields, was_truncated = _code_field(
                self.lean_code, "lean_code", verbose=verbose
            )
            result.update(fields)
            if was_truncated:
                result["truncated"] = True
                result["hint"] = (
                    "Call again with verbose=True to get the full lean_code."
                )
        if self.project_id is not None:
            result["project_id"] = self.project_id
        if self.percent_complete is not None:
            result["percent_complete"] = self.percent_complete
        return result
