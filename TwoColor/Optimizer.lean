import TwoColor.EnergySpace
import TwoColor.LinearAlgebra.LeastSquares

/-!
# Attainment of the finite Dirichlet variational problem

The proof projects the weighted exchange gradient onto the orthogonal complement
of gradients of interior corrections. The image is finite dimensional, hence
closed, even at `δ = 0`. This gives an actual admissible minimizing correction,
its Euler equations, and uniqueness of its weighted gradient. No uniqueness of
the correction as a function is asserted.
-/

noncomputable section

namespace TwoColor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The uniquely determined optimal weighted gradient, linear in the affine source. -/
def optimalGradient (ρ : Density) (E : Finset (V × V)) (I : Finset V) (δ : ℝ) :
    (Config V → ℝ) →ₗ[ℝ] BondSpace E :=
  LeastSquares.residual (weightedGradient ρ E δ) (correctionSpace I)

theorem exists_correction_optimalGradient (ρ : Density) (E : Finset (V × V))
    (I : Finset V) (δ : ℝ) (ℓ : Config V → ℝ) :
    ∃ φ : Config V → ℝ, DependsOnlyOn I φ ∧
      weightedGradient ρ E δ (ℓ + φ) = optimalGradient ρ E I δ ℓ :=
  LeastSquares.exists_correction (weightedGradient ρ E δ) (correctionSpace I) ℓ

/-- The infimum defining the primal energy is a concrete squared projection norm. -/
theorem primalEnergy_eq_norm_sq (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    primalEnergy ρ E I δ ℓ = ‖optimalGradient ρ E I δ ℓ‖ ^ 2 := by
  obtain ⟨φ, hφ, hopt⟩ := exists_correction_optimalGradient ρ E I δ ℓ
  apply le_antisymm
  · calc
      _ ≤ energy ρ E δ (ℓ + φ) := primalEnergy_le_competitor ρ E I hδ ℓ φ hφ
      _ = ‖weightedGradient ρ E δ (ℓ + φ)‖ ^ 2 := (weightedGradient_norm_sq ρ E hδ _).symm
      _ = _ := by rw [hopt]
  · apply le_csInf (admissibleEnergies_nonempty ρ E I δ ℓ)
    rintro q ⟨ψ, hψ, rfl⟩
    rw [← weightedGradient_norm_sq ρ E hδ]
    exact LeastSquares.norm_sq_residual_le (weightedGradient ρ E δ) (correctionSpace I) ℓ ψ hψ

/-- Attainment, including the physical zero-stirring case. -/
theorem exists_primal_optimizer (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    ∃ φ : Config V → ℝ, DependsOnlyOn I φ ∧
      primalEnergy ρ E I δ ℓ = energy ρ E δ (ℓ + φ) := by
  obtain ⟨φ, hφ, hopt⟩ := exists_correction_optimalGradient ρ E I δ ℓ
  refine ⟨φ, hφ, ?_⟩
  rw [primalEnergy_eq_norm_sq ρ E I hδ, ← weightedGradient_norm_sq ρ E hδ, hopt]

/-- A selected minimizing correction; only its existence, not a numerical algorithm, is used. -/
def primalOptimizer (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) : Config V → ℝ :=
  (exists_primal_optimizer ρ E I hδ ℓ).choose

theorem primalOptimizer_dependsOnlyOn (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    DependsOnlyOn I (primalOptimizer ρ E I hδ ℓ) :=
  (exists_primal_optimizer ρ E I hδ ℓ).choose_spec.1

theorem primalOptimizer_energy (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    energy ρ E δ (ℓ + primalOptimizer ρ E I hδ ℓ) = primalEnergy ρ E I δ ℓ :=
  (exists_primal_optimizer ρ E I hδ ℓ).choose_spec.2.symm

/-- A correction attains the infimum exactly when its weighted gradient is the projection. -/
theorem primal_optimizer_iff_gradient (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ φ : Config V → ℝ) (hφ : DependsOnlyOn I φ) :
    primalEnergy ρ E I δ ℓ = energy ρ E δ (ℓ + φ) ↔
      weightedGradient ρ E δ (ℓ + φ) = optimalGradient ρ E I δ ℓ := by
  constructor
  · intro h
    apply (LeastSquares.minimizes_iff_eq_residual
      (weightedGradient ρ E δ) (correctionSpace I) ℓ φ hφ).mp
    intro ψ hψ
    rw [weightedGradient_norm_sq ρ E hδ, weightedGradient_norm_sq ρ E hδ, ← h]
    exact primalEnergy_le_competitor ρ E I hδ ℓ ψ hψ
  · intro h
    rw [primalEnergy_eq_norm_sq ρ E I hδ, ← weightedGradient_norm_sq ρ E hδ, h]

/-- The Euler equations are necessary and sufficient for an admissible correction to minimize. -/
theorem primal_optimizer_iff_harmonic (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ φ : Config V → ℝ) (hφ : DependsOnlyOn I φ) :
    primalEnergy ρ E I δ ℓ = energy ρ E δ (ℓ + φ) ↔
      ∀ ψ : Config V → ℝ, DependsOnlyOn I ψ → energyForm ρ E δ (ℓ + φ) ψ = 0 := by
  rw [primal_optimizer_iff_gradient ρ E I hδ ℓ φ hφ]
  exact (LeastSquares.eq_residual_iff_normal
    (weightedGradient ρ E δ) (correctionSpace I) ℓ φ hφ).trans (by
      simp only [mem_correctionSpace, weightedGradient_inner ρ E hδ])

theorem primalOptimizer_harmonic (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ ψ : Config V → ℝ) (hψ : DependsOnlyOn I ψ) :
    energyForm ρ E δ (ℓ + primalOptimizer ρ E I hδ ℓ) ψ = 0 :=
  (primal_optimizer_iff_harmonic ρ E I hδ ℓ _ (primalOptimizer_dependsOnlyOn ρ E I hδ ℓ)).mp
    (primalOptimizer_energy ρ E I hδ ℓ).symm ψ hψ

/-- Minimizers have the same weighted exchange gradient; corrections can differ by a kernel. -/
theorem primal_optimizer_gradient_unique (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ φ ψ : Config V → ℝ)
    (hφ : DependsOnlyOn I φ) (hψ : DependsOnlyOn I ψ)
    (hφmin : primalEnergy ρ E I δ ℓ = energy ρ E δ (ℓ + φ))
    (hψmin : primalEnergy ρ E I δ ℓ = energy ρ E δ (ℓ + ψ)) :
    weightedGradient ρ E δ (ℓ + φ) = weightedGradient ρ E δ (ℓ + ψ) :=
  ((primal_optimizer_iff_gradient ρ E I hδ ℓ φ hφ).mp hφmin).trans
    ((primal_optimizer_iff_gradient ρ E I hδ ℓ ψ hψ).mp hψmin).symm

end TwoColor
