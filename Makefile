# Aristotle MCP Server - Makefile
# ================================
# Build, test, and development commands for the Aristotle theorem prover MCP server

.PHONY: help install install-dev install-api install-all \
        check lint format type-check \
        test test-mock test-api test-all test-lean \
        run run-mock \
        build clean clean-all \
        verify venv

# Default target
.DEFAULT_GOAL := help

# Colors for terminal output
BLUE := \033[0;34m
GREEN := \033[0;32m
YELLOW := \033[0;33m
RED := \033[0;31m
NC := \033[0m # No Color

# Project paths
SRC_DIR := src/aristotle_mcp
TEST_DIR := tests
LEAN_PROJECT := tests/lean_project

# Virtual environment detection
VENV_DIR := .venv
VENV_BIN := $(VENV_DIR)/bin
PYTHON := $(if $(wildcard $(VENV_BIN)/python),$(VENV_BIN)/python,python)
PIP := $(if $(wildcard $(VENV_BIN)/pip),$(VENV_BIN)/pip,pip)

# Tools (use venv versions if available)
RUFF := $(if $(wildcard $(VENV_BIN)/ruff),$(VENV_BIN)/ruff,ruff)
MYPY := $(if $(wildcard $(VENV_BIN)/mypy),$(VENV_BIN)/mypy,mypy)
PYTEST := $(if $(wildcard $(VENV_BIN)/pytest),$(VENV_BIN)/pytest,pytest)

#------------------------------------------------------------------------------
# Help
#------------------------------------------------------------------------------

help: ## Show this help message
	@echo "$(BLUE)Aristotle MCP Server$(NC)"
	@echo "====================="
	@echo ""
	@echo "$(GREEN)Setup:$(NC)"
	@grep -E '^(venv|install[a-z-]*):.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  $(YELLOW)%-18s$(NC) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(GREEN)Code Quality:$(NC)"
	@grep -E '^(check|lint|format|type-check):.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  $(YELLOW)%-18s$(NC) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(GREEN)Testing:$(NC)"
	@grep -E '^(test[a-z-]*):.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  $(YELLOW)%-18s$(NC) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(GREEN)Run:$(NC)"
	@grep -E '^(run[a-z-]*):.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  $(YELLOW)%-18s$(NC) %s\n", $$1, $$2}'
	@echo ""
	@echo "$(GREEN)Build:$(NC)"
	@grep -E '^(build|clean[a-z-]*|verify):.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  $(YELLOW)%-18s$(NC) %s\n", $$1, $$2}'

#------------------------------------------------------------------------------
# Installation
#------------------------------------------------------------------------------

venv: ## Create virtual environment
	python -m venv $(VENV_DIR)
	$(PIP) install --upgrade pip

install: ## Install package in editable mode (minimal)
	$(PIP) install -e .

install-dev: ## Install with development dependencies
	$(PIP) install -e ".[dev]"

install-api: ## Install with Aristotle API support
	$(PIP) install -e ".[api]"

install-all: ## Install with all dependencies (dev + api)
	$(PIP) install -e ".[dev,api]"

#------------------------------------------------------------------------------
# Code Quality
#------------------------------------------------------------------------------

check: lint type-check ## Run all code quality checks

lint: ## Run linter (ruff)
	$(RUFF) check $(SRC_DIR) $(TEST_DIR)

format: ## Auto-fix linting issues (ruff)
	$(RUFF) check --fix $(SRC_DIR) $(TEST_DIR)
	$(RUFF) format $(SRC_DIR) $(TEST_DIR)

type-check: ## Run type checker (mypy)
	$(MYPY) $(SRC_DIR)

#------------------------------------------------------------------------------
# Testing
#------------------------------------------------------------------------------

test: test-mock ## Run default tests (mock mode only)

test-mock: ## Run mock mode tests (no API key needed)
	ARISTOTLE_MOCK=true $(PYTEST) $(TEST_DIR)/test_mock.py -v

test-api: ## Run live API tests (requires ARISTOTLE_API_KEY)
	@if [ -z "$$ARISTOTLE_API_KEY" ]; then \
		echo "$(RED)Error: ARISTOTLE_API_KEY not set$(NC)"; \
		echo "Set it in .env or export it: export ARISTOTLE_API_KEY=your_key"; \
		exit 1; \
	fi
	$(PYTEST) $(TEST_DIR)/test_api.py $(TEST_DIR)/test_api_tools.py -v --timeout=120

test-all: test-mock ## Run all tests (mock + API if key available)
	@if [ -n "$$ARISTOTLE_API_KEY" ]; then \
		echo "$(GREEN)Running API tests...$(NC)"; \
		$(PYTEST) $(TEST_DIR)/test_api.py $(TEST_DIR)/test_api_tools.py -v --timeout=120; \
	else \
		echo "$(YELLOW)Skipping API tests (ARISTOTLE_API_KEY not set)$(NC)"; \
	fi

test-lean: ## Verify the test Lean project builds
	@echo "$(BLUE)Building Lean test project...$(NC)"
	cd $(LEAN_PROJECT) && lake build
	@echo "$(GREEN)Lean project builds successfully$(NC)"

#------------------------------------------------------------------------------
# Run Server
#------------------------------------------------------------------------------

run: ## Run the MCP server
	$(PYTHON) -m aristotle_mcp

run-mock: ## Run the MCP server in mock mode
	ARISTOTLE_MOCK=true $(PYTHON) -m aristotle_mcp

#------------------------------------------------------------------------------
# Build & Distribution
#------------------------------------------------------------------------------

build: clean ## Build wheel package
	$(PYTHON) -m build

clean: ## Remove build artifacts
	rm -rf build/
	rm -rf dist/
	rm -rf *.egg-info/
	rm -rf src/*.egg-info/
	find . -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete 2>/dev/null || true

clean-all: clean ## Remove all generated files (build + test artifacts)
	rm -rf .pytest_cache/
	rm -rf .mypy_cache/
	rm -rf .ruff_cache/
	rm -rf $(LEAN_PROJECT)/.lake/
	rm -rf $(LEAN_PROJECT)/build/
	find $(LEAN_PROJECT) -name "*_aristotle.lean" -delete 2>/dev/null || true

verify: check test test-lean ## Full verification (lint + type-check + tests + lean)
	@echo ""
	@echo "$(GREEN)All checks passed!$(NC)"
