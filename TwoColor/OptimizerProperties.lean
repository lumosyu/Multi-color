import TwoColor.Optimizer

/-!
# Energy gaps and centered finite-volume optimizers

The excess energy of an admissible correction is exactly the energy of its
difference from an optimizer. Subtracting a constant leaves all exchange
gradients unchanged, so an optimizer can be chosen with zero equilibrium mean.
These statements include the degenerate rate `δ = 0` and assert no uniqueness
of corrections as functions.
-/

noncomputable section

namespace TwoColor

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem weightedGradient_const (ρ : Density) (E : Finset (V × V))
    (δ c : ℝ) : weightedGradient ρ E δ (fun _ : Config V => c) = 0 := by
  ext z
  simp [weightedGradient_apply]

/-- Exact variational energy gap for any admissible correction. -/
theorem primal_energy_gap (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ φ : Config V → ℝ) (hφ : DependsOnlyOn I φ) :
    energy ρ E δ (ℓ + φ) = primalEnergy ρ E I δ ℓ +
      energy ρ E δ (φ - primalOptimizer ρ E I hδ ℓ) := by
  have hopt : weightedGradient ρ E δ (ℓ + primalOptimizer ρ E I hδ ℓ) =
      optimalGradient ρ E I δ ℓ :=
    (primal_optimizer_iff_gradient ρ E I hδ ℓ _
      (primalOptimizer_dependsOnlyOn ρ E I hδ ℓ)).mp
        (primalOptimizer_energy ρ E I hδ ℓ).symm
  have hdiff : weightedGradient ρ E δ (ℓ + φ) - optimalGradient ρ E I δ ℓ =
      weightedGradient ρ E δ (φ - primalOptimizer ρ E I hδ ℓ) := by
    rw [← hopt, map_add, map_add, map_sub]
    abel
  calc
    energy ρ E δ (ℓ + φ) = ‖weightedGradient ρ E δ (ℓ + φ)‖ ^ 2 :=
      (weightedGradient_norm_sq ρ E hδ _).symm
    _ = ‖optimalGradient ρ E I δ ℓ‖ ^ 2 +
        ‖weightedGradient ρ E δ (ℓ + φ) - optimalGradient ρ E I δ ℓ‖ ^ 2 :=
      LeastSquares.norm_sq_decomposition (weightedGradient ρ E δ) (correctionSpace I) ℓ φ hφ
    _ = primalEnergy ρ E I δ ℓ + energy ρ E δ (φ - primalOptimizer ρ E I hδ ℓ) := by
      rw [hdiff, weightedGradient_norm_sq ρ E hδ, primalEnergy_eq_norm_sq ρ E I hδ]

/-- A chosen optimizer centered under the finite product equilibrium. -/
def centeredPrimalOptimizer (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) : Config V → ℝ :=
  fun η => primalOptimizer ρ E I hδ ℓ η - expectation ρ (primalOptimizer ρ E I hδ ℓ)

theorem centeredPrimalOptimizer_dependsOnlyOn (ρ : Density) (E : Finset (V × V))
    (I : Finset V) {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    DependsOnlyOn I (centeredPrimalOptimizer ρ E I hδ ℓ) := by
  intro η ζ h
  unfold centeredPrimalOptimizer
  rw [primalOptimizer_dependsOnlyOn ρ E I hδ ℓ η ζ h]

theorem centeredPrimalOptimizer_mean_zero (ρ : Density) (E : Finset (V × V))
    (I : Finset V) {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    expectation ρ (centeredPrimalOptimizer ρ E I hδ ℓ) = 0 := by
  unfold centeredPrimalOptimizer
  rw [expectation_sub, expectation_const, sub_self]

theorem centeredPrimalOptimizer_gradient (ρ : Density) (E : Finset (V × V))
    (I : Finset V) {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    weightedGradient ρ E δ (ℓ + centeredPrimalOptimizer ρ E I hδ ℓ) =
      weightedGradient ρ E δ (ℓ + primalOptimizer ρ E I hδ ℓ) := by
  change weightedGradient ρ E δ (ℓ + (primalOptimizer ρ E I hδ ℓ -
    (fun _ => expectation ρ (primalOptimizer ρ E I hδ ℓ)))) = _
  rw [map_add, map_sub, weightedGradient_const, sub_zero, ← map_add]

theorem centeredPrimalOptimizer_energy (ρ : Density) (E : Finset (V × V))
    (I : Finset V) {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    energy ρ E δ (ℓ + centeredPrimalOptimizer ρ E I hδ ℓ) = primalEnergy ρ E I δ ℓ := by
  rw [← weightedGradient_norm_sq ρ E hδ, centeredPrimalOptimizer_gradient,
    weightedGradient_norm_sq ρ E hδ, primalOptimizer_energy]

theorem exists_mean_zero_primal_optimizer (ρ : Density) (E : Finset (V × V))
    (I : Finset V) {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    ∃ φ : Config V → ℝ, DependsOnlyOn I φ ∧ expectation ρ φ = 0 ∧
      energy ρ E δ (ℓ + φ) = primalEnergy ρ E I δ ℓ :=
  ⟨centeredPrimalOptimizer ρ E I hδ ℓ,
    centeredPrimalOptimizer_dependsOnlyOn ρ E I hδ ℓ,
    centeredPrimalOptimizer_mean_zero ρ E I hδ ℓ,
    centeredPrimalOptimizer_energy ρ E I hδ ℓ⟩

end TwoColor
