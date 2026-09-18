# Two-color exclusion in Lean

An in-progress Lean 4 formalization of *Algebraic approximation for two-color
exclusion and a quenched invariance principle for the tagged particle*
(September 2026 manuscript).

**Status: verified foundations. Theorems 1.1 and 1.2 are not yet formalized or
proved.** See [FORMALIZATION.md](FORMALIZATION.md) for the exact source version,
paper-to-code correspondence, limitations, and remaining proof obligations.

## Checked mathematics

- Concrete configurations, exchanges, occupation indicators, and stirring rates.
- Positive densities, covariance determinant and positivity, and the
  occupation/color decomposition.
- Outgoing lattice cubes, interior and endpoint sets, and affine gradients.
- Finite product equilibrium, reversibility, and the generator–energy identity.
- The normalized scalar Dirichlet cell problem, competitor bounds, and stirring
  monotonicity.
- Scalar exponent, exponential-kernel, and summability estimates from Section 9.

All mathematical modules are imported by [TwoColor.lean](TwoColor.lean).
The original [MultiColorLean.lean](MultiColorLean.lean) installation theorem is
preserved as a small compatibility wrapper.

## Build and audit

Install [Lean through Elan](https://lean-lang.org/install/manual/), then run these
commands from the repository folder (PowerShell or a Unix shell):

```sh
lake exe cache get
lake build --wfail
lake env lean Audit.lean
```

The toolchain is Lean **4.26.0**. Mathlib is pinned to **v4.26.0**, commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; all dependency revisions are recorded
in [lake-manifest.json](lake-manifest.json). The generated `.lake/` directory is
not committed.

[Audit.lean](Audit.lean) checks all project declarations, including their
transitive dependencies. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. Proof placeholders and added axioms make the audit fail.
GitHub Actions runs both the build and this audit on pushes and pull requests.
The initial local results are recorded in [VERIFICATION.md](VERIFICATION.md).

The project organization is inspired by the requested reference,
[Manhattan-Transience](https://github.com/nitromannitol/Manhattan-Transience).
Its mathematical results are not dependencies of this development.
