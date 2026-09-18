import TwoColor.Susceptibility
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Real.StarOrdered

/-!
# Positive susceptibility and symmetric conductivity normalization

This file constructs the inverse positive square root of
`K = 2 Σ ⊗ I_d` and hence the normalized conductivity
`a = K⁻¹ᐟ² A K⁻¹ᐟ²` from equation (1.2). Positivity is proved from the
positive density vector, not assumed as an extra hypothesis.

The construction applies to any conductivity matrix `A`; its realization by
the cell variational problem belongs to the cell-matrix module.
-/

noncomputable section

open scoped Matrix Kronecker MatrixOrder

namespace TwoColor

namespace Density

variable (ρ : Density)

theorem covariance_isHermitian : ρ.covariance.IsHermitian := by
  change ρ.covarianceᴴ = ρ.covariance
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using ρ.covariance_isSymm.eq

/-- The covariance quadratic form proved in `Density` gives matrix positivity. -/
theorem covariance_posDef : ρ.covariance.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos ρ.covariance_isHermitian
  intro x hx
  have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_cases h0 : x 0 = 0
    · right
      intro h1
      apply hx
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · exact Or.inl h0
  have hpos := ρ.covarianceEnergy_pos_of_ne hne
  rw [ρ.covarianceEnergy_eq_matrix] at hpos
  simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_succ] using hpos

theorem susceptibility_posDef (d : ℕ) : (ρ.susceptibility d).PosDef :=
  ρ.covariance_posDef.kronecker
    (Matrix.PosDef.one : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef)

theorem fluctuationMatrix_posDef (d : ℕ) : (ρ.fluctuationMatrix d).PosDef :=
  (ρ.susceptibility_posDef d).smul (by norm_num : (0 : ℝ) < 2)

theorem fluctuationMatrix_sqrt_posDef (d : ℕ) :
    (CFC.sqrt (ρ.fluctuationMatrix d)).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp
    (ρ.fluctuationMatrix_posDef d).isStrictlyPositive.sqrt

/-- The inverse of the positive matrix square root of `K`, denoted `K⁻¹ᐟ²`
in the paper. -/
def covarianceNormalization (d : ℕ) : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ :=
  (CFC.sqrt (ρ.fluctuationMatrix d))⁻¹

theorem covarianceNormalization_posDef (d : ℕ) :
    (ρ.covarianceNormalization d).PosDef :=
  (ρ.fluctuationMatrix_sqrt_posDef d).inv

theorem covarianceNormalization_isSymm (d : ℕ) :
    (ρ.covarianceNormalization d).IsSymm := by
  change (ρ.covarianceNormalization d)ᵀ = ρ.covarianceNormalization d
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (ρ.covarianceNormalization_posDef d).isHermitian.eq

/-- The defining normalization identity `K⁻¹ᐟ² K K⁻¹ᐟ² = I`. -/
theorem covarianceNormalization_mul_fluctuationMatrix (d : ℕ) :
    ρ.covarianceNormalization d * ρ.fluctuationMatrix d *
      ρ.covarianceNormalization d = 1 := by
  have hunit := (ρ.fluctuationMatrix_sqrt_posDef d).isUnit
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hleft := Matrix.nonsing_inv_mul (CFC.sqrt (ρ.fluctuationMatrix d)) hdet
  have hright := Matrix.mul_nonsing_inv (CFC.sqrt (ρ.fluctuationMatrix d)) hdet
  calc
    ρ.covarianceNormalization d * ρ.fluctuationMatrix d *
        ρ.covarianceNormalization d =
        (CFC.sqrt (ρ.fluctuationMatrix d))⁻¹ *
          (CFC.sqrt (ρ.fluctuationMatrix d) * CFC.sqrt (ρ.fluctuationMatrix d)) *
          (CFC.sqrt (ρ.fluctuationMatrix d))⁻¹ := by
      rw [CFC.sqrt_mul_sqrt_self _ (ρ.fluctuationMatrix_posDef d).posSemidef.nonneg]
      rfl
    _ = 1 := by
      rw [← Matrix.mul_assoc, hleft, Matrix.one_mul, hright]

end Density

/-- The symmetric normalization of a conductivity matrix in equation (1.2). -/
def normalizedConductivity (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) :
    Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ :=
  ρ.covarianceNormalization d * A * ρ.covarianceNormalization d

/-- The normalized quadratic form is the conductivity quadratic form with
the slope changed by `K⁻¹ᐟ²`, as in equation (1.2). -/
theorem normalizedConductivity_quadratic (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ)
    (p : Fin 2 × Fin d → ℝ) :
    p ⬝ᵥ ((normalizedConductivity ρ A) *ᵥ p) =
      (ρ.covarianceNormalization d *ᵥ p) ⬝ᵥ
        (A *ᵥ (ρ.covarianceNormalization d *ᵥ p)) := by
  have hvec : p ᵥ* ρ.covarianceNormalization d = ρ.covarianceNormalization d *ᵥ p := by
    simpa only [(ρ.covarianceNormalization_isSymm d).eq] using
      Matrix.vecMul_transpose (ρ.covarianceNormalization d) p
  rw [normalizedConductivity, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, hvec]

theorem normalizedConductivity_sub (ρ : Density) {d : ℕ}
    (A B : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) :
    normalizedConductivity ρ (A - B) =
      normalizedConductivity ρ A - normalizedConductivity ρ B := by
  simp only [normalizedConductivity, mul_sub, sub_mul]

theorem normalizedConductivity_isSymm (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) (hA : A.IsSymm) :
    (normalizedConductivity ρ A).IsSymm := by
  change (ρ.covarianceNormalization d * A * ρ.covarianceNormalization d)ᵀ =
    ρ.covarianceNormalization d * A * ρ.covarianceNormalization d
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    (ρ.covarianceNormalization_isSymm d).eq, hA.eq, Matrix.mul_assoc]

theorem normalizedConductivity_posSemidef (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) (hA : A.PosSemidef) :
    (normalizedConductivity ρ A).PosSemidef := by
  simpa only [normalizedConductivity,
    (ρ.covarianceNormalization_posDef d).isHermitian.eq] using
    hA.conjTranspose_mul_mul_same (ρ.covarianceNormalization d)

theorem normalizedConductivity_posDef (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) (hA : A.PosDef) :
    (normalizedConductivity ρ A).PosDef := by
  have hinj : Function.Injective (ρ.covarianceNormalization d).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (ρ.covarianceNormalization_posDef d).isUnit
  simpa only [normalizedConductivity,
    (ρ.covarianceNormalization_posDef d).isHermitian.eq] using
    hA.conjTranspose_mul_mul_same hinj

/-- The normalization maps `K` to the identity. -/
theorem normalizedConductivity_fluctuationMatrix (ρ : Density) (d : ℕ) :
    normalizedConductivity ρ (ρ.fluctuationMatrix d) = 1 :=
  ρ.covarianceNormalization_mul_fluctuationMatrix d

end TwoColor
