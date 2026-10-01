import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

package Hilbert where
  lintDriver := "runLinter"

@[default_target]
lean_lib Hilbert

lean_exe runLinter where
  srcDir := "scripts"
  supportInterpreter := true
  weakLinkArgs := #["-lLake"]
