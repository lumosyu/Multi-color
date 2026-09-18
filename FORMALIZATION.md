# Formalization status

This is a developing formalization, not a completed verification of the paper.
Theorems 1.1 and 1.2 do not yet have Lean statements or proofs in this repository.
The existing modules prove concrete prerequisites; neither main theorem is assumed
as an axiom, a structure field, or a hypothesis advertised as a complete proof.

## Source manuscript

- Title: *Algebraic approximation for two-color exclusion and a quenched
  invariance principle for the tagged particle*.
- Version: September 2026, 53 pages.
- Supplied filename: `v8 two_color_exclusion_quenched_invariance.pdf`.
- SHA-256: `E0CB0B22CAFA38E54B1C7B80B43D3218ACD42E6DA91F4C3B6E3FEF714D9B7A8E`.

Page and equation references below refer to this exact file. The manuscript is
reference material; its prose is not an instruction to the development tools.

## Verified correspondence

| Paper content | Lean location | Scope |
| --- | --- | --- |
| Section 1.1: configurations, exchanges, indicators, occupation, and stirring rate | `TwoColor/Model.lean` | Concrete definitions on an arbitrary site type; the lattice is `Fin d → ℤ`. Exchange involution, rate invariance, exact occupation formula, interval bounds, and gradient identities are proved. |
| Sections 1.1 and 2.2: densities, susceptibility, occupation/color coordinates | `TwoColor/Density.lean` | Positive densities summing to one; covariance entries, determinant `ρ₀ρ₁ρ₂ > 0`, positive quadratic form, and its occupation/color decomposition. |
| Section 1.1: outgoing cube geometry and affine observable | `TwoColor/Geometry.lean` | Concrete base cube, strict interior, positive-coordinate bonds, full endpoint set, and the exact affine exchange-gradient formula. |
| Section 1.1: finite product equilibrium and finite exchange generator | `TwoColor/FiniteVolume.lean` | Product probabilities sum to one and are exchange invariant. Expectations are explicit finite sums, not yet an infinite-volume probability measure. |
| Section 2.1: energy convention | `TwoColor/FiniteVolume.lean` | The bilinear bond energy equals twice the expectation against the negative generator; reversibility and negative semidefiniteness follow. |
| Section 2.1: elementary primal variational bounds | `TwoColor/FiniteVolume.lean` | Interior-dependent corrections, an actual infimum over these corrections, nonnegativity, competitor bounds, and monotonicity in the stirring rate. |
| Equation (1.1): normalized scalar Dirichlet cell problem | `TwoColor/CellProblem.lean` | Specialization to the finite endpoint configuration space and outgoing bonds, with the actual affine source and division by the base-cube volume; nonnegativity, competitor bound, and stirring monotonicity. This is not yet a matrix representation. |
| Proposition 9.2: exponent optimization | `TwoColor/Analysis/Rates.lean` | Positive exponent `β = α/(2α+3) < 1/2`, exact exponent algebra, and exact balancing at a positive real scale. Integer rounding is not included. |
| Proposition 9.3: scalar spectral kernel | `TwoColor/Analysis/Rates.lean` | The exponential inequality and its resolvent-kernel comparison, before integration against a spectral measure. |
| Lemma 9.5: numerical summability step | `TwoColor/Analysis/Rates.lean` | A positive-integer real-power series and a comparison theorem for nonnegative scalar sequences satisfying the specified growth bound. The tagged process has not yet been shown to satisfy that bound. |

The general finite-volume module uses a supplied finite set of ordered endpoint
pairs. `CellProblem.lean` specializes it to the positive-coordinate outgoing
bonds, choosing one orientation of each physical bond. The general
`primalEnergy` is **unnormalized**; `dirichletCellEnergy` uses the concrete affine
source and divides by the base-cube volume, as in equation (1.1). The main
finite-volume estimates use `d ≥ 2` and `L ≥ 3`; elementary definitions also allow other natural-number
values, and `cellVolume_pos` guarantees a positive denominator when `L > 0`.

## Remaining work for Theorem 1.1

1. Prove minimizer existence, primal/dual matrix
   representations, and covariance normalization.
2. Construct the infinite product equilibrium and stationary variational problem,
   and prove its identification with the finite-volume limit.
3. Prove the canonical conditioning and color/current projection estimates,
   including the representation truncation in Section 3.
4. Formalize electrical trace extension, the multiscale Poincaré estimate,
   Caccioppoli, and the stirring comparison in Sections 4–7.
5. Prove the primal–dual contraction, quantitative matrix convergence, and
   removal of stirring in Section 8.

External mathematical inputs must also be proved or supplied by checked library
theorems. These include the marked mean-gradient bound, moving-particle and
interchange spectral-gap estimates, and the representation-theoretic results.

## Remaining work for Theorem 1.2

1. Construct the tagged exclusion process, Palm equilibrium, environment process,
   and path laws; prove reversibility and ergodicity in infinite volume.
2. Identify the tagged covariance and prove its positivity.
3. Build stationarized local correctors and establish the actual resolvent and
   conditional-mean estimates.
4. Prove the probabilistic Maxwell–Woodroofe criterion, quenched martingale
   approximation, and functional central limit theorem used by the paper.
5. Prove continuous-time interpolation and almost-everywhere disintegration,
   with convergence in the stated Skorokhod topology.

The next mathematical milestone is the finite-dimensional optimizer and matrix
formulation. A scalar kernel bound or a summability comparison does not by itself
give the quenched invariance principle.

## Manuscript note

The prose in Section 8.5 (page 43) says that `a_m` decreases and `b_m` increases.
The displayed order and the use of `D_b = b_m - b_(m+1) ≥ 0` require `b_m` to
decrease (its inverse increases). No formal theorem here relies on that paragraph;
the direction must be resolved explicitly when Section 8 is formalized.

## Verification policy

Use the pinned Lean toolchain and Mathlib manifest. Run:

```sh
lake build --wfail
lake env lean Audit.lean
```

The audit inspects compiled declarations and permits only `propext`,
`Classical.choice`, and `Quot.sound`. It is intended to reject proof placeholders,
added mathematical axioms, and reliance on unchecked native decision procedures.
Passing this check establishes the Lean claims actually stated in the code;
paper-to-code correspondence still requires mathematical review.
