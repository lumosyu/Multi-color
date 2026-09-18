import TwoColor.CellProblem
import TwoColor.Optimizer
import TwoColor.LinearAlgebra.GramMatrix
import TwoColor.Susceptibility
import TwoColor.Normalization

/-!
# Finite-volume conductivity and physical diffusion matrices

The conductivity matrix is the volume-normalized Gram matrix of the optimal
weighted gradient of the affine source. Its quadratic form is proved equal to
the concrete infimum in equation (1.1). The physical diffusion matrix then uses
the invertible susceptibility normalization in equation (1.2).

These are finite-volume matrices. No infinite-volume convergence, strictly
positive coercivity bound, or identification with tagged self-diffusion is
asserted here.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TwoColor

/-- The optimal residual depends linearly on the spatial/color slope vector. -/
def cellResidual (ρ : Density) (d L : ℕ) (δ : ℝ) :
    CellSlope d →ₗ[ℝ] BondSpace (cellBonds d L) :=
  (optimalGradient ρ (cellBonds d L) (cellInterior d L) δ).comp (cellAffineMap d L)

/-- The symmetric finite-volume conductivity matrix `A_Q^δ` of equation (1.1). -/
def cellConductivity (ρ : Density) (d L : ℕ) (δ : ℝ) :
    Matrix (SlopeIndex d) (SlopeIndex d) ℝ :=
  normalizedLinearGramMatrix (cellVolume d L) (cellResidual ρ d L δ)

theorem cellConductivity_isSymm (ρ : Density) (d L : ℕ) (δ : ℝ) :
    (cellConductivity ρ d L δ).IsSymm :=
  normalizedLinearGramMatrix_isSymm _ _

theorem cellConductivity_posSemidef (ρ : Density) (d L : ℕ) (δ : ℝ) :
    (cellConductivity ρ d L δ).PosSemidef :=
  normalizedLinearGramMatrix_posSemidef (cellVolume_nonneg d L) _

/-- The constructed matrix represents the original cell infimum, with its exact normalization. -/
theorem cellConductivity_quadratic (ρ : Density) (d L : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (p : CellSlope d) :
    p ⬝ᵥ ((cellConductivity ρ d L δ) *ᵥ p) =
      dirichletCellEnergy ρ d L δ (fun j => p (0, j)) (fun j => p (1, j)) := by
  rw [cellConductivity, normalizedLinearGramMatrix_quadratic, dirichletCellEnergy,
    primalEnergy_eq_norm_sq ρ _ _ hδ]
  rfl

/-- Uniqueness among symmetric matrices satisfying the cell variational formula. -/
theorem cellConductivity_unique (ρ : Density) (d L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (A : Matrix (SlopeIndex d) (SlopeIndex d) ℝ) (hA : A.IsSymm)
    (hform : ∀ p : CellSlope d, p ⬝ᵥ (A *ᵥ p) =
      dirichletCellEnergy ρ d L δ (fun j => p (0, j)) (fun j => p (1, j))) :
    A = cellConductivity ρ d L δ := by
  apply symmetricMatrix_eq_of_quadratic_eq hA (cellConductivity_isSymm ρ d L δ)
  intro p
  rw [hform, cellConductivity_quadratic ρ d L hδ]

/-- The scalar stirring comparison is also a positive-semidefinite matrix comparison. -/
theorem cellConductivity_mono (ρ : Density) (d L : ℕ)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    (cellConductivity ρ d L δ - cellConductivity ρ d L ε).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((cellConductivity_posSemidef ρ d L δ).isHermitian.sub
      (cellConductivity_posSemidef ρ d L ε).isHermitian)
  intro p
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  rw [cellConductivity_quadratic ρ d L (hε.trans hεδ), cellConductivity_quadratic ρ d L hε]
  exact sub_nonneg.mpr (dirichletCellEnergy_mono ρ d L hε hεδ _ _)

/-- The actual finite-cell infimum is attained by an interior-dependent correction. -/
theorem exists_cell_optimizer (ρ : Density) (d L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (pRed pBlue : Fin d → ℝ) :
    ∃ φ : Config (CellSite d L) → ℝ, DependsOnlyOn (cellInterior d L) φ ∧
      dirichletCellEnergy ρ d L δ pRed pBlue =
        cellCompetitorEnergy ρ d L δ pRed pBlue φ := by
  obtain ⟨φ, hφ, heq⟩ := exists_primal_optimizer ρ (cellBonds d L) (cellInterior d L)
    hδ (cellAffineSource d L pRed pBlue)
  refine ⟨φ, hφ, ?_⟩
  exact congrArg (fun q => q / cellVolume d L) heq

/-- The finite-volume physical diffusion matrix `D_Q^δ = A_Q^δ (Σ⁻¹ ⊗ I_d)`. -/
def cellDiffusionMatrix (ρ : Density) (d L : ℕ) (δ : ℝ) :
    Matrix (SlopeIndex d) (SlopeIndex d) ℝ :=
  physicalDiffusionMatrix ρ (cellConductivity ρ d L δ)

theorem cellDiffusionMatrix_recover (ρ : Density) (d L : ℕ) (δ : ℝ) :
    cellDiffusionMatrix ρ d L δ * ρ.susceptibility d = cellConductivity ρ d L δ :=
  physicalDiffusionMatrix_recover ρ _

/-- The product with susceptibility, rather than necessarily `D` itself, is symmetric. -/
theorem cellDiffusionMatrix_weighted_isSymm (ρ : Density) (d L : ℕ) (δ : ℝ) :
    (cellDiffusionMatrix ρ d L δ * ρ.susceptibility d).IsSymm := by
  rw [cellDiffusionMatrix_recover]
  exact cellConductivity_isSymm ρ d L δ

/-- The physical diffusion matrix recovers the variational form in the paper's convention. -/
theorem cellDiffusionMatrix_quadratic (ρ : Density) (d L : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (p : CellSlope d) :
    p ⬝ᵥ ((cellDiffusionMatrix ρ d L δ * ρ.susceptibility d) *ᵥ p) =
      dirichletCellEnergy ρ d L δ (fun j => p (0, j)) (fun j => p (1, j)) := by
  rw [cellDiffusionMatrix_recover, cellConductivity_quadratic ρ d L hδ]

/-- The covariance-normalized finite-volume matrix `a_Q^δ = K⁻¹ᐟ² A_Q^δ K⁻¹ᐟ²`. -/
def cellNormalizedConductivity (ρ : Density) (d L : ℕ) (δ : ℝ) :
    Matrix (SlopeIndex d) (SlopeIndex d) ℝ :=
  normalizedConductivity ρ (cellConductivity ρ d L δ)

theorem cellNormalizedConductivity_isSymm (ρ : Density) (d L : ℕ) (δ : ℝ) :
    (cellNormalizedConductivity ρ d L δ).IsSymm :=
  normalizedConductivity_isSymm ρ _ (cellConductivity_isSymm ρ d L δ)

theorem cellNormalizedConductivity_posSemidef (ρ : Density) (d L : ℕ) (δ : ℝ) :
    (cellNormalizedConductivity ρ d L δ).PosSemidef :=
  normalizedConductivity_posSemidef ρ _ (cellConductivity_posSemidef ρ d L δ)

/-- The normalized cell matrix uses precisely the inverse-square-root-transformed slope. -/
theorem cellNormalizedConductivity_quadratic (ρ : Density) (d L : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (p : CellSlope d) :
    p ⬝ᵥ ((cellNormalizedConductivity ρ d L δ) *ᵥ p) =
      dirichletCellEnergy ρ d L δ
        (fun j => (ρ.covarianceNormalization d *ᵥ p) (0, j))
        (fun j => (ρ.covarianceNormalization d *ᵥ p) (1, j)) := by
  rw [cellNormalizedConductivity, normalizedConductivity_quadratic,
    cellConductivity_quadratic ρ d L hδ]

theorem cellNormalizedConductivity_mono (ρ : Density) (d L : ℕ)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    (cellNormalizedConductivity ρ d L δ - cellNormalizedConductivity ρ d L ε).PosSemidef := by
  have h := normalizedConductivity_posSemidef ρ _ (cellConductivity_mono ρ d L hε hεδ)
  simpa only [cellNormalizedConductivity, normalizedConductivity,
    Matrix.mul_sub, Matrix.sub_mul] using h

end TwoColor
