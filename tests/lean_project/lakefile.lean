import Lake
open Lake DSL

package «test_project» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

@[default_target]
lean_lib «TestProject» where
  globs := #[.submodules `TestProject]
