"""Type stubs for aristotlelib - Harmonic's Aristotle theorem prover SDK.

IMPORTANT: These stubs were audited against aristotlelib version 0.6.x.
All signatures verified via runtime inspection on 2025-01-13.
"""

from datetime import datetime
from enum import Enum
from pathlib import Path

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

    FORMAL_LEAN = 2
    INFORMAL = 3

class Project:
    """A proof project in the Aristotle system.

    This is a Pydantic model with the following fields.
    """

    project_id: str
    status: ProjectStatus
    created_at: datetime
    last_updated_at: datetime
    percent_complete: int | None
    file_name: str | None
    description: str | None

    @classmethod
    async def create(
        cls,
        context_file_paths: list[Path] | list[str] | None = None,
        validate_lean_project_root: bool = True,
        project_input_type: ProjectInputType = ...,
    ) -> "Project":
        """Create a new proof project."""
        ...

    @classmethod
    async def from_id(cls, project_id: str) -> "Project":
        """Load an existing project by ID."""
        ...

    @classmethod
    async def list_projects(
        cls,
        pagination_key: str | None = None,
        limit: int = 30,
        status: ProjectStatus | list[ProjectStatus] | None = None,
    ) -> tuple[list["Project"], str | None]:
        """List projects. Returns (projects, next_pagination_key)."""
        ...

    @classmethod
    async def prove_from_file(
        cls,
        *,
        input_file_path: Path | str | None = None,
        input_content: str | None = None,
        auto_add_imports: bool = True,
        context_file_paths: list[Path] | list[str] | None = None,
        context_is_folder: bool = False,
        validate_lean_project: bool = True,
        wait_for_completion: bool = True,
        polling_interval_seconds: int = 30,
        max_polling_failures: int = 3,
        output_file_path: Path | str | None = None,
        project_input_type: ProjectInputType = ...,
        formal_input_context: Path | str | None = None,
    ) -> str:
        """Prove from file or content. Always returns output path string."""
        ...

    async def add_context(
        self,
        context_file_paths: list[Path] | list[str],
        batch_size: int = 10,
        validate_lean_project_root: bool = True,
        project_root: Path | None = None,
    ) -> None:
        """Add context files to the project."""
        ...

    async def solve(
        self,
        input_file_path: Path | str | None = None,
        input_content: str | None = None,
        formal_input_context: Path | str | None = None,
    ) -> None:
        """Submit code to solve."""
        ...

    async def refresh(self) -> None:
        """Refresh project status from the API."""
        ...

    async def wait_for_completion(
        self,
        output_file_path: Path | str,
        polling_interval_seconds: int = 30,
        max_polling_failures: int = 3,
    ) -> str:
        """Wait for the proof to complete. Returns output path."""
        ...

    async def get_solution(self, output_path: Path | str | None = None) -> Path:
        """Get the solution and write it to a file. Returns the path."""
        ...
