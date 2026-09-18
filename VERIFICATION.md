# Verification record

Verified locally on Windows on 2026-09-18, using the repository's pinned Lean
4.26.0 and Mathlib v4.26.0 toolchain.

## Build

```text
lake build --wfail
Build completed successfully (1988 jobs).
```

Both the `TwoColor` library and the `MultiColorLean` compatibility entry point
built without warnings. The six mathematical modules are all imported by the
library root. The installed Mathlib compilation cache was reused; this was not
a build of Mathlib from source.

## Compiled-declaration audit

```text
lake env lean Audit.lean
Project axiom audit passed: 253 declarations, 198 theorems, 52 definitions/opaque constants.
Transitive axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean environment counts, including generated declarations and equation
lemmas, not counts of independent results from the manuscript. The audit covers
both project namespaces and declarations belonging to their imported modules,
including private helpers. New mathematical files must be imported by the root.

During development, three separate negative probes confirmed that the audit
rejects a direct project axiom, an external custom axiom used indirectly by a
project theorem, and a proof placeholder hidden in a project definition. None
of those probes is part of the mathematical library.

## Mathematical correspondence

Read-only reviews checked the microscopic definitions, covariance algebra,
finite product weights, generator normalization, variational admissibility and
lower bounds, outgoing geometry, and scalar analytic estimates against the
manuscript. The comparison is documented in
[FORMALIZATION.md](FORMALIZATION.md).

The main theorems remain unformalized. The checks above certify the prerequisite
statements actually present in Lean; they do not certify the manuscript's full
convergence or quenched invariance results. GitHub CI is configured separately;
the local results above are not a claim about a completed remote CI run.
