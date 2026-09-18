import TwoColor.Density
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FinCases

/-!
# Susceptibility and the physical diffusion convention

Equation (1.2) uses the spatial susceptibility `Σ ⊗ I_d`, the fluctuation
normalization `K = 2 Σ ⊗ I_d`, and the physical diffusion matrix
`D = A (Σ⁻¹ ⊗ I_d)`. We construct these matrices and prove that the
normalization is invertible at every positive density.

The physical matrix need not be symmetric. Its product with susceptibility
recovers the symmetric conductivity matrix. This file does not construct the
conductivity matrix from the cell problem or claim an infinite-volume limit.
-/

noncomputable section

open scoped Kronecker Matrix

namespace TwoColor

namespace Density

variable (ρ : Density)

theorem covariance_isSymm : ρ.covariance.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem covariance_det_isUnit : IsUnit ρ.covariance.det :=
  isUnit_iff_ne_zero.mpr (ne_of_gt ρ.covariance_det_pos)

theorem covariance_mul_inv : ρ.covariance * ρ.covariance⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ρ.covariance_det_isUnit

theorem covariance_inv_mul : ρ.covariance⁻¹ * ρ.covariance = 1 :=
  Matrix.nonsing_inv_mul _ ρ.covariance_det_isUnit

/-- The covariance matrix extended to the two color slopes in `d` dimensions. -/
def susceptibility (d : ℕ) : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ :=
  ρ.covariance ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℝ)

theorem susceptibility_apply (d : ℕ) (i j : Fin 2 × Fin d) :
    ρ.susceptibility d i j = ρ.covariance i.1 j.1 *
      (if i.2 = j.2 then 1 else 0) := by
  simp [susceptibility, Matrix.one_apply]

theorem susceptibility_isSymm (d : ℕ) : (ρ.susceptibility d).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [susceptibility_apply, susceptibility_apply, ρ.covariance_isSymm.apply]
  simp [eq_comm]

theorem susceptibility_det (d : ℕ) :
    (ρ.susceptibility d).det = (ρ.vacancy * ρ.red * ρ.blue) ^ d := by
  simp [susceptibility, Matrix.det_kronecker, ρ.covariance_det]

theorem susceptibility_det_pos (d : ℕ) : 0 < (ρ.susceptibility d).det := by
  rw [susceptibility_det]
  exact pow_pos (mul_pos (mul_pos ρ.vacancy_pos ρ.red_pos) ρ.blue_pos) _

theorem susceptibility_det_isUnit (d : ℕ) : IsUnit (ρ.susceptibility d).det :=
  isUnit_iff_ne_zero.mpr (ne_of_gt (ρ.susceptibility_det_pos d))

theorem susceptibility_isUnit (d : ℕ) : IsUnit (ρ.susceptibility d) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (ρ.susceptibility_det_isUnit d)

theorem susceptibility_mul_inv (d : ℕ) :
    ρ.susceptibility d * (ρ.susceptibility d)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (ρ.susceptibility_det_isUnit d)

theorem susceptibility_inv_mul (d : ℕ) :
    (ρ.susceptibility d)⁻¹ * ρ.susceptibility d = 1 :=
  Matrix.nonsing_inv_mul _ (ρ.susceptibility_det_isUnit d)

/-- The inverse has exactly the Kronecker-product form in equation (1.2). -/
theorem susceptibility_inv (d : ℕ) :
    (ρ.susceptibility d)⁻¹ = ρ.covariance⁻¹ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℝ) := by
  apply Matrix.inv_eq_left_inv
  rw [susceptibility, ← Matrix.mul_kronecker_mul, ρ.covariance_inv_mul,
    Matrix.one_mul, Matrix.one_kronecker_one]

theorem susceptibility_inv_isSymm (d : ℕ) : ((ρ.susceptibility d)⁻¹).IsSymm := by
  change ((ρ.susceptibility d)⁻¹)ᵀ = _
  rw [Matrix.transpose_nonsing_inv, (ρ.susceptibility_isSymm d).eq]

/-- The matrix `K = 2 Σ ⊗ I_d` in equation (1.2). -/
def fluctuationMatrix (d : ℕ) : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ :=
  (2 : ℝ) • ρ.susceptibility d

theorem fluctuationMatrix_eq (d : ℕ) :
    ρ.fluctuationMatrix d = ((2 : ℝ) • ρ.covariance) ⊗ₖ
      (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [Matrix.smul_kronecker]
  rfl

end Density

/-- Physical diffusion convention `D = A (Σ⁻¹ ⊗ I_d)`.
The input `A` is the conductivity matrix, not assumed here to come from a cell. -/
def physicalDiffusionMatrix (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) :
    Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ :=
  A * (ρ.susceptibility d)⁻¹

theorem physicalDiffusionMatrix_eq_kronecker (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) :
    physicalDiffusionMatrix ρ A =
      A * (ρ.covariance⁻¹ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  rw [physicalDiffusionMatrix, ρ.susceptibility_inv]

/-- Multiplication by susceptibility recovers the conductivity matrix. -/
theorem physicalDiffusionMatrix_recover (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) :
    physicalDiffusionMatrix ρ A * ρ.susceptibility d = A := by
  rw [physicalDiffusionMatrix, Matrix.mul_assoc, ρ.susceptibility_inv_mul,
    Matrix.mul_one]

theorem physicalDiffusionMatrix_eq_iff (ρ : Density) {d : ℕ}
    (A D : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) :
    D = physicalDiffusionMatrix ρ A ↔ D * ρ.susceptibility d = A := by
  constructor
  · rintro rfl
    exact physicalDiffusionMatrix_recover ρ A
  · intro h
    rw [physicalDiffusionMatrix, ← h, Matrix.mul_assoc,
      ρ.susceptibility_mul_inv, Matrix.mul_one]

/-- Weighted symmetry is inherited from conductivity; ordinary symmetry of `D`
is intentionally not asserted. -/
theorem physicalDiffusionMatrix_weighted_isSymm (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) (hA : A.IsSymm) :
    (physicalDiffusionMatrix ρ A * ρ.susceptibility d).IsSymm := by
  rw [physicalDiffusionMatrix_recover]
  exact hA

theorem physicalDiffusionMatrix_weighted_symmetry (ρ : Density) {d : ℕ}
    (A : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) (hA : A.IsSymm) :
    physicalDiffusionMatrix ρ A * ρ.susceptibility d =
      ρ.susceptibility d * (physicalDiffusionMatrix ρ A)ᵀ := by
  have h := congrArg Matrix.transpose (physicalDiffusionMatrix_recover ρ A)
  rw [Matrix.transpose_mul, (ρ.susceptibility_isSymm d).eq, hA.eq] at h
  rw [physicalDiffusionMatrix_recover, h]

/-- The conductivity normalization `A = K` corresponds to physical diffusion `2I`.
Identifying the full-stirring optimizer with `K` is a separate cell theorem. -/
theorem physicalDiffusionMatrix_fluctuationMatrix (ρ : Density) (d : ℕ) :
    physicalDiffusionMatrix ρ (ρ.fluctuationMatrix d) =
      (2 : ℝ) • (1 : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℝ) := by
  rw [physicalDiffusionMatrix, Density.fluctuationMatrix, Matrix.smul_mul,
    ρ.susceptibility_mul_inv]

end TwoColor
