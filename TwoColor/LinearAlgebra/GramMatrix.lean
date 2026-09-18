import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith

/-!
# Matrix representation of a linear residual energy

A real linear residual map on finitely many slope coordinates has a symmetric
positive-semidefinite Gram matrix. Its quadratic form is exactly the squared
norm of the residual. Nonnegative scalar and inverse-volume normalizations are
included for finite-cell energy matrices.
-/

noncomputable section

open scoped BigOperators InnerProductSpace Matrix

namespace TwoColor

set_option autoImplicit false

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Gram matrix of a real linear map, in the standard coordinate basis. -/
def linearGramMatrix (R : (ι → ℝ) →ₗ[ℝ] H) : Matrix ι ι ℝ :=
  Matrix.gram ℝ (fun i => R (Pi.single i 1))

omit [Fintype ι] in
@[simp] theorem linearGramMatrix_apply (R : (ι → ℝ) →ₗ[ℝ] H) (i j : ι) :
    linearGramMatrix R i j = ⟪R (Pi.single i 1), R (Pi.single j 1)⟫_ℝ := rfl

omit [Fintype ι] in
theorem linearGramMatrix_isSymm (R : (ι → ℝ) →ₗ[ℝ] H) :
    (linearGramMatrix R).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact real_inner_comm _ _

omit [Fintype ι] in
theorem linearGramMatrix_isHermitian (R : (ι → ℝ) →ₗ[ℝ] H) :
    (linearGramMatrix R).IsHermitian :=
  Matrix.isHermitian_gram ℝ _

theorem linearGramMatrix_posSemidef (R : (ι → ℝ) →ₗ[ℝ] H) :
    (linearGramMatrix R).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

/-- Expansion of a linear image in the images of the coordinate vectors. -/
theorem linearMap_eq_sum_single (R : (ι → ℝ) →ₗ[ℝ] H) (x : ι → ℝ) :
    R x = ∑ i, x i • R (Pi.single i 1) := by
  calc
    R x = R (∑ i, x i • (Pi.single i (1 : ℝ) : ι → ℝ)) := by
      congr 1
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    _ = _ := by simp only [map_sum, map_smul]

theorem linearGramMatrix_bilinear (R : (ι → ℝ) →ₗ[ℝ] H) (x y : ι → ℝ) :
    x ⬝ᵥ ((linearGramMatrix R) *ᵥ y) = ⟪R x, R y⟫_ℝ := by
  simpa only [linearGramMatrix, star_trivial, ← linearMap_eq_sum_single R x,
    ← linearMap_eq_sum_single R y] using
    Matrix.star_dotProduct_gram_mulVec (fun i => R (Pi.single i 1)) x y

theorem linearGramMatrix_quadratic (R : (ι → ℝ) →ₗ[ℝ] H) (x : ι → ℝ) :
    x ⬝ᵥ ((linearGramMatrix R) *ᵥ x) = ‖R x‖ ^ 2 := by
  rw [linearGramMatrix_bilinear, real_inner_self_eq_norm_sq]

/-- A real symmetric matrix is determined by all values of its quadratic form. -/
theorem symmetricMatrix_eq_of_quadratic_eq {A B : Matrix ι ι ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x)) : A = B := by
  have hdiag (i : ι) : A i i = B i i := by
    simpa [Matrix.mulVec_single_one, single_one_dotProduct] using h (Pi.single i 1)
  apply Matrix.ext
  intro i j
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_single_one, single_one_dotProduct] at hij
  change A i i + A j i + (A i j + A j j) =
    B i i + B j i + (B i j + B j j) at hij
  rw [hA.apply i j, hB.apply i j] at hij
  linarith [hdiag i, hdiag j]

/-- Uniqueness of the symmetric matrix representing the residual norm. -/
theorem linearGramMatrix_unique (R : (ι → ℝ) →ₗ[ℝ] H) {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) (h : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) = ‖R x‖ ^ 2) :
    A = linearGramMatrix R := by
  apply symmetricMatrix_eq_of_quadratic_eq hA (linearGramMatrix_isSymm R)
  intro x
  rw [h, linearGramMatrix_quadratic]

/-- Scalar normalization of the residual Gram matrix. -/
def scaledLinearGramMatrix (c : ℝ) (R : (ι → ℝ) →ₗ[ℝ] H) : Matrix ι ι ℝ :=
  c • linearGramMatrix R

omit [Fintype ι] in
@[simp] theorem scaledLinearGramMatrix_apply (c : ℝ) (R : (ι → ℝ) →ₗ[ℝ] H)
    (i j : ι) : scaledLinearGramMatrix c R i j =
      c * ⟪R (Pi.single i 1), R (Pi.single j 1)⟫_ℝ := rfl

omit [Fintype ι] in
theorem scaledLinearGramMatrix_isSymm (c : ℝ) (R : (ι → ℝ) →ₗ[ℝ] H) :
    (scaledLinearGramMatrix c R).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [scaledLinearGramMatrix_apply, real_inner_comm]

theorem scaledLinearGramMatrix_posSemidef {c : ℝ} (hc : 0 ≤ c)
    (R : (ι → ℝ) →ₗ[ℝ] H) : (scaledLinearGramMatrix c R).PosSemidef :=
  (linearGramMatrix_posSemidef R).smul hc

theorem scaledLinearGramMatrix_bilinear (c : ℝ) (R : (ι → ℝ) →ₗ[ℝ] H)
    (x y : ι → ℝ) :
    x ⬝ᵥ ((scaledLinearGramMatrix c R) *ᵥ y) = c * ⟪R x, R y⟫_ℝ := by
  simp only [scaledLinearGramMatrix, Matrix.smul_mulVec, dotProduct_smul,
    linearGramMatrix_bilinear, smul_eq_mul]

theorem scaledLinearGramMatrix_quadratic (c : ℝ) (R : (ι → ℝ) →ₗ[ℝ] H)
    (x : ι → ℝ) :
    x ⬝ᵥ ((scaledLinearGramMatrix c R) *ᵥ x) = c * ‖R x‖ ^ 2 := by
  rw [scaledLinearGramMatrix_bilinear, real_inner_self_eq_norm_sq]

/-- Divide the residual Gram matrix by a real cell volume. -/
def normalizedLinearGramMatrix (volume : ℝ) (R : (ι → ℝ) →ₗ[ℝ] H) : Matrix ι ι ℝ :=
  scaledLinearGramMatrix volume⁻¹ R

omit [Fintype ι] in
theorem normalizedLinearGramMatrix_isSymm (volume : ℝ) (R : (ι → ℝ) →ₗ[ℝ] H) :
    (normalizedLinearGramMatrix volume R).IsSymm :=
  scaledLinearGramMatrix_isSymm _ R

theorem normalizedLinearGramMatrix_posSemidef {volume : ℝ} (hvolume : 0 ≤ volume)
    (R : (ι → ℝ) →ₗ[ℝ] H) : (normalizedLinearGramMatrix volume R).PosSemidef :=
  scaledLinearGramMatrix_posSemidef (inv_nonneg.mpr hvolume) R

theorem normalizedLinearGramMatrix_quadratic (volume : ℝ) (R : (ι → ℝ) →ₗ[ℝ] H)
    (x : ι → ℝ) :
    x ⬝ᵥ ((normalizedLinearGramMatrix volume R) *ᵥ x) = ‖R x‖ ^ 2 / volume := by
  rw [normalizedLinearGramMatrix, scaledLinearGramMatrix_quadratic]
  exact (div_eq_inv_mul _ _).symm

end TwoColor
