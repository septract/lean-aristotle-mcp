"""Test the Aristotle API directly (requires API key)."""

import asyncio
import os

import pytest
from dotenv import load_dotenv

load_dotenv()

# Skip all tests if no API key
pytestmark = pytest.mark.skipif(
    not os.environ.get("ARISTOTLE_API_KEY"),
    reason="ARISTOTLE_API_KEY not set",
)


@pytest.fixture
def simple_proof() -> str:
    return """
theorem simple_add : 2 + 2 = 4 := by
  sorry
"""


async def test_list_projects() -> None:
    """Test listing existing projects."""
    from aristotlelib import Project

    projects, _pagination = await Project.list_projects()
    assert isinstance(projects, list)
    if projects:
        p = projects[0]
        assert hasattr(p, "project_id")
        assert hasattr(p, "status")
        assert hasattr(p, "percent_complete")
        print(f"\nFound {len(projects)} projects")
        print(f"Latest: {p.project_id} - {p.status.name} ({p.percent_complete}%)")


async def test_poll_existing_project() -> None:
    """Test polling an existing project."""
    from aristotlelib import Project

    projects, _ = await Project.list_projects()
    if not projects:
        pytest.skip("No existing projects to poll")

    project = await Project.from_id(str(projects[0].project_id))
    await project.refresh()

    print(f"\nProject: {project.project_id}")
    print(f"Status: {project.status.name}")
    print(f"Percent: {project.percent_complete}%")

    assert project.status.name in [
        "NOT_STARTED",
        "QUEUED",
        "IN_PROGRESS",
        "COMPLETE",
        "FAILED",
        "PENDING_RETRY",
    ]


@pytest.mark.timeout(180)  # 3 minute timeout
async def test_submit_and_poll(simple_proof: str) -> None:
    """Test submitting a proof and polling for completion."""
    from aristotlelib import Project

    # Submit
    project = await Project.create()
    await project.solve(input_content=simple_proof)

    print(f"\nSubmitted: {project.project_id}")
    print(f"Initial: {project.status.name} ({project.percent_complete}%)")

    # Poll until complete or timeout (3 minutes max)
    for i in range(90):
        await asyncio.sleep(2)
        await project.refresh()
        print(f"Poll {i + 1}: {project.status.name} ({project.percent_complete}%)")

        if project.status.name in ("COMPLETE", "FAILED"):
            break

    assert project.status.name == "COMPLETE", f"Expected COMPLETE, got {project.status.name}"

    # Get solution
    solution_path = await project.get_solution(output_path="/tmp/test_solution.lean")
    assert solution_path is not None
    with open(solution_path) as f:
        solution = f.read()
    print(f"\nSolution:\n{solution}")
    assert "sorry" not in solution.lower() or "was proved" in solution.lower()
