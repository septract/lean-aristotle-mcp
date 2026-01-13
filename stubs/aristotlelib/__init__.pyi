"""Type stubs for aristotlelib - Harmonic's Aristotle theorem prover SDK."""

from enum import Enum
from typing import Literal, overload
from uuid import UUID

class ProjectStatus(Enum):
    """Status of a proof project."""

    NOT_STARTED = "NOT_STARTED"
    QUEUED = "QUEUED"
    IN_PROGRESS = "IN_PROGRESS"
    COMPLETE = "COMPLETE"
    FAILED = "FAILED"
    PENDING_RETRY = "PENDING_RETRY"

class ProjectInputType(Enum):
    """Type of input for a proof project."""

    FORMAL = "FORMAL"
    INFORMAL = "INFORMAL"

class Pagination:
    """Pagination info from list operations."""

    ...

class Project:
    """A proof project in the Aristotle system."""

    project_id: UUID
    status: ProjectStatus
    percent_complete: int | None

    @classmethod
    async def create(cls) -> Project:
        """Create a new proof project."""
        ...

    @classmethod
    async def from_id(cls, project_id: str) -> Project:
        """Load an existing project by ID."""
        ...

    @classmethod
    async def list_projects(cls) -> tuple[list[Project], Pagination]:
        """List all projects."""
        ...

    @overload
    @classmethod
    async def prove_from_file(
        cls,
        input_file_path: str,
        output_file_path: str | None = ...,
        auto_add_imports: bool = ...,
        *,
        wait_for_completion: Literal[True] = ...,
        project_input_type: ProjectInputType | None = ...,
        formal_input_context: str | None = ...,
        **kwargs: object,
    ) -> str:
        """Prove a Lean file, waiting for completion. Returns the output path."""
        ...

    @overload
    @classmethod
    async def prove_from_file(
        cls,
        input_file_path: str,
        output_file_path: str | None = ...,
        auto_add_imports: bool = ...,
        *,
        wait_for_completion: Literal[False],
        project_input_type: ProjectInputType | None = ...,
        formal_input_context: str | None = ...,
        **kwargs: object,
    ) -> Project:
        """Prove a Lean file without waiting. Returns the Project for polling."""
        ...

    @overload
    @classmethod
    async def prove_from_file(
        cls,
        input_file_path: str,
        output_file_path: str | None = ...,
        auto_add_imports: bool = ...,
        *,
        wait_for_completion: bool,
        project_input_type: ProjectInputType | None = ...,
        formal_input_context: str | None = ...,
        **kwargs: object,
    ) -> str | Project:
        """Prove a Lean file. Returns path or Project depending on wait_for_completion."""
        ...

    async def solve(self, input_content: str) -> None:
        """Submit code to solve."""
        ...

    async def refresh(self) -> None:
        """Refresh project status from the API."""
        ...

    async def add_context(self, context_files: list[str]) -> None:
        """Add context files to the project."""
        ...

    async def wait_for_completion(self, output_file_path: str) -> str | None:
        """Wait for the proof to complete and write the solution."""
        ...

    async def get_solution(self, output_path: str | None = ...) -> str | None:
        """Get the solution and write it to a file."""
        ...
