"""Result models for the Aristotle MCP server."""

from __future__ import annotations

from dataclasses import dataclass

# Type for JSON-serializable result dictionaries
ResultValue = str | int | None
ResultDict = dict[str, ResultValue]


@dataclass
class ProveResult:
    """Result from a prove operation."""

    status: str  # proved | counterexample | failed | error | submitted | in_progress | queued
    code: str | None = None
    counterexample: str | None = None
    project_id: str | None = None
    percent_complete: int | None = None
    message: str = ""

    def to_dict(self) -> ResultDict:
        """Convert to dictionary for JSON serialization."""
        result: ResultDict = {"status": self.status, "message": self.message}
        if self.code is not None:
            result["code"] = self.code
        if self.counterexample is not None:
            result["counterexample"] = self.counterexample
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

    status: str  # formalized | proved | failed | error
    lean_code: str | None = None
    message: str = ""

    def to_dict(self) -> ResultDict:
        """Convert to dictionary for JSON serialization."""
        result: ResultDict = {"status": self.status, "message": self.message}
        if self.lean_code is not None:
            result["lean_code"] = self.lean_code
        return result
