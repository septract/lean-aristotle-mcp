import Lake
open Lake DSL

package «test_project» where
  version := v!"0.1.0"

@[default_target]
lean_lib «TestProject» where
  globs := #[.submodules `TestProject]
