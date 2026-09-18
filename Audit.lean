import MultiColorLean
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom audit for the full project

Run `lake env lean Audit.lean` after building the library. The command fails if
there are no project declarations or theorems, if any audited declaration is
itself an axiom, or if any audited declaration transitively depends on an axiom
other than `propext`, `Classical.choice`, and `Quot.sound`.

The scan covers the entire `TwoColor` and `MultiColorLean` namespaces, including
generated constants. It also covers private or differently named declarations
belonging to imported modules under those names. The root `MultiColorLean`
module imports the full library; new modules must remain reachable from that
root. A shared dependency traversal checks both declaration
types and bodies, so a hidden `sorry` in a definition or hypothesis is rejected.
This is a proof-integrity check, not a check that statements express the paper's
main theorems; that correspondence still requires mathematical review.
-/

open Lean Elab Command in
elab "#audit_project_axioms" : command => do
  let env ← getEnv
  let namespacePrefixes : Array Name := #[`TwoColor, `MultiColorLean]
  let isProjectName := fun name => namespacePrefixes.any (fun ns => ns.isPrefixOf name)
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Array Name := #[]
  let mut theoremCount := 0
  let mut definitionCount := 0
  for (name, info) in env.constants do
    let ownedByProject := match env.getModuleIdxFor? name with
      | some idx => isProjectName env.header.moduleNames[idx.toNat]!
      | none => false
    if isProjectName name || ownedByProject then
      declarations := declarations.push name
      match info with
      | .axiomInfo _ => throwError "Project audit rejected a declared axiom: {name}"
      | .thmInfo _ => theoremCount := theoremCount + 1
      | .defnInfo _ => definitionCount := definitionCount + 1
      | .opaqueInfo _ => definitionCount := definitionCount + 1
      | _ => pure ()
  if declarations.isEmpty || theoremCount == 0 then
    throwError "Project audit found no declarations or no theorems; check the library import."
  let (_, state) :=
    ((declarations.forM Lean.CollectAxioms.collect).run env).run {}
  let unexpected := state.axioms.filter (fun name => !allowed.contains name)
  unless unexpected.isEmpty do
    throwError "Project audit rejected transitive axioms: {unexpected.toList}"
  logInfo m!"Project axiom audit passed: {declarations.size} declarations, \
    {theoremCount} theorems, {definitionCount} definitions/opaque constants."
  logInfo m!"Transitive axioms: {state.axioms.qsort Name.lt |>.toList}"

#audit_project_axioms
