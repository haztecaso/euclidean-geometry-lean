import Batteries.Tactic.Lint
import Lake.CLI.Main

open Lean Core Elab Command Batteries.Tactic.Lint
open System (FilePath)

open Lake

/-- Returns the root modules of default targets in the Lake workspace. -/
def resolveDefaultRootModules : IO (Array Name) := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  let defaultTargetModules := workspace.root.defaultTargets.flatMap fun target =>
    if let some lib := workspace.root.findLeanLib? target then
      lib.roots
    else if let some exe := workspace.root.findLeanExe? target then
      #[exe.config.root]
    else
      #[]
  return defaultTargetModules

/-- Run the Batteries linter on a given module. -/
unsafe def runLinterOnModule (module : Name) : IO Unit := do
  initSearchPath (← findSysroot)
  let lintModule := `Batteries.Tactic.Lint
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024) (loadExts := true)
  let ctx := { fileName := "", fileMap := default }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let results ← lintCore decls linters
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
          s!"in {module}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {module}."

unsafe def main (args : List String) : IO Unit := do
  let modules ← match args with
    | [] => resolveDefaultRootModules
    | _  => pure (args.map String.toName).toArray
  modules.forM runLinterOnModule
  IO.Process.exit 0
