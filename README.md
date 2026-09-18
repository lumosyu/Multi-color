# MultiColorLean

Lean and Mathlib setup for the two-color exclusion formalization.

Verified on 2026-09-18: `lake build` completed successfully (7,744 jobs).
The example theorem uses only `propext`, `Classical.choice`, and `Quot.sound`;
its axiom audit contains no `sorryAx`.

- Lean: `leanprover/lean4:v4.26.0`
- Mathlib: tag `v4.26.0`; exact dependency commits are recorded in `lake-manifest.json`.
- Lean is installed for the Windows user through Elan in `C:\Users\23049\.elan`.
- Mathlib is a project dependency in `.lake/packages/mathlib`, rather than a global library.

## Build

Open a new PowerShell window in this folder and run:

```powershell
lean --version
lake build
```

The installation test in `MultiColorLean.lean` proves that
`0 < α / (2 * α + 3) < 1 / 2` when `α > 0` and prints the proof's axioms.
It is a setup test, not a formalization of the paper's main theorems.

To restore compiled Mathlib files after downloading the project on another machine:

```powershell
lake exe cache get
lake build
```

Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` together so that
Lean, Mathlib, and their dependencies stay compatible. The `.lake` folder is
generated locally and should not be committed to GitHub.

Official installation documentation: https://lean-lang.org/install/manual/
