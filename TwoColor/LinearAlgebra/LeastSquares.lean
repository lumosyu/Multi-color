import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Finite-dimensional least squares with a correction subspace

Given a linear observation map `T` and an admissible correction subspace `S`,
the optimal observed residual is the orthogonal projection of `T x` onto
the orthogonal complement of `S.map T`. Only the observation space needs to
be finite dimensional. The map `T` may have a kernel, so corrections need not
be unique; the optimal observed residual is unique.
-/

noncomputable section

namespace TwoColor.LeastSquares

variable {F H : Type*} [AddCommGroup F] [Module ℝ F]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The optimal observed residual, as a linear map in the affine source. -/
def residual (T : F →ₗ[ℝ] H) (S : Submodule ℝ F) : F →ₗ[ℝ] H :=
  (S.map T)ᗮ.starProjection.toLinearMap.comp T

theorem residual_eq (T : F →ₗ[ℝ] H) (S : Submodule ℝ F) (x : F) :
    residual T S x = T x - (S.map T).starProjection (T x) := by
  exact Submodule.starProjection_orthogonal_val (T x)

theorem residual_mem_orthogonal (T : F →ₗ[ℝ] H) (S : Submodule ℝ F) (x : F) :
    residual T S x ∈ (S.map T)ᗮ :=
  Submodule.starProjection_apply_mem _ _

theorem residual_inner_eq_zero (T : F →ₗ[ℝ] H) (S : Submodule ℝ F)
    (x ψ : F) (hψ : ψ ∈ S) : inner ℝ (residual T S x) (T ψ) = 0 := by
  exact (Submodule.mem_orthogonal' _ _).mp (residual_mem_orthogonal T S x)
    (T ψ) (Submodule.mem_map.mpr ⟨ψ, hψ, rfl⟩)

/-- An admissible correction attains the projected residual. -/
theorem exists_correction (T : F →ₗ[ℝ] H) (S : Submodule ℝ F) (x : F) :
    ∃ φ ∈ S, T (x + φ) = residual T S x := by
  obtain ⟨ψ, hψ, hTψ⟩ := Submodule.mem_map.mp
    ((S.map T).starProjection_apply_mem (T x))
  refine ⟨-ψ, S.neg_mem hψ, ?_⟩
  rw [map_add, map_neg, hTψ, residual_eq, sub_eq_add_neg]

theorem residual_eq_zero_of_mem (T : F →ₗ[ℝ] H) (S : Submodule ℝ F)
    (ψ : F) (hψ : ψ ∈ S) : residual T S ψ = 0 := by
  rw [residual_eq,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_map.mpr ⟨ψ, hψ, rfl⟩)]
  exact sub_self _

theorem residual_add_correction (T : F →ₗ[ℝ] H) (S : Submodule ℝ F)
    (x ψ : F) (hψ : ψ ∈ S) : residual T S (x + ψ) = residual T S x := by
  rw [map_add, residual_eq_zero_of_mem T S ψ hψ, add_zero]

theorem difference_mem_image (T : F →ₗ[ℝ] H) (S : Submodule ℝ F)
    (x ψ : F) (hψ : ψ ∈ S) : T (x + ψ) - residual T S x ∈ S.map T := by
  have hmem := (S.map T).add_mem ((S.map T).starProjection_apply_mem (T x))
    (Submodule.mem_map.mpr ⟨ψ, hψ, rfl⟩)
  convert hmem using 1
  rw [map_add, residual_eq]
  abel

/-- The energy gap is the squared distance from the unique optimal observed residual. -/
theorem norm_sq_decomposition (T : F →ₗ[ℝ] H) (S : Submodule ℝ F)
    (x ψ : F) (hψ : ψ ∈ S) :
    ‖T (x + ψ)‖ ^ 2 = ‖residual T S x‖ ^ 2 +
      ‖T (x + ψ) - residual T S x‖ ^ 2 := by
  have horth : inner ℝ (residual T S x) (T (x + ψ) - residual T S x) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (residual_mem_orthogonal T S x)
      _ (difference_mem_image T S x ψ hψ)
  have hsum : residual T S x + (T (x + ψ) - residual T S x) = T (x + ψ) := by
    abel
  simpa only [hsum, pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth

theorem norm_sq_residual_le (T : F →ₗ[ℝ] H) (S : Submodule ℝ F)
    (x ψ : F) (hψ : ψ ∈ S) : ‖residual T S x‖ ^ 2 ≤ ‖T (x + ψ)‖ ^ 2 := by
  rw [norm_sq_decomposition T S x ψ hψ]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The optimal observed residual is characterized by the normal equations. -/
theorem eq_residual_iff_normal (T : F →ₗ[ℝ] H) (S : Submodule ℝ F)
    (x φ : F) (hφ : φ ∈ S) :
    T (x + φ) = residual T S x ↔
      ∀ ψ ∈ S, inner ℝ (T (x + φ)) (T ψ) = 0 := by
  constructor
  · intro h ψ hψ
    rw [h]
    exact residual_inner_eq_zero T S x ψ hψ
  · intro h
    have hm : T (x + φ) ∈ (S.map T)ᗮ := by
      apply (Submodule.mem_orthogonal' _ _).mpr
      intro y hy
      obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.mp hy
      exact h ψ hψ
    have hp : residual T S (x + φ) = T (x + φ) :=
      Submodule.starProjection_eq_self_iff.mpr hm
    exact hp.symm.trans (residual_add_correction T S x φ hφ)

/-- A correction is minimizing exactly when it realizes the projected residual. -/
theorem minimizes_iff_eq_residual (T : F →ₗ[ℝ] H) (S : Submodule ℝ F)
    (x φ : F) (hφ : φ ∈ S) :
    (∀ ψ ∈ S, ‖T (x + φ)‖ ^ 2 ≤ ‖T (x + ψ)‖ ^ 2) ↔
      T (x + φ) = residual T S x := by
  constructor
  · intro hmin
    obtain ⟨ψ, hψ, hψeq⟩ := exists_correction T S x
    have hle := hmin ψ hψ
    rw [hψeq] at hle
    have hdecomp := norm_sq_decomposition T S x φ hφ
    have hzero : ‖T (x + φ) - residual T S x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖T (x + φ) - residual T S x‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  · intro heq ψ hψ
    rw [heq]
    exact norm_sq_residual_le T S x ψ hψ

/-- The finite-dimensional least-squares Euler equations are necessary and sufficient. -/
theorem minimizes_iff_normal (T : F →ₗ[ℝ] H) (S : Submodule ℝ F)
    (x φ : F) (hφ : φ ∈ S) :
    (∀ ψ ∈ S, ‖T (x + φ)‖ ^ 2 ≤ ‖T (x + ψ)‖ ^ 2) ↔
      ∀ ψ ∈ S, inner ℝ (T (x + φ)) (T ψ) = 0 :=
  (minimizes_iff_eq_residual T S x φ hφ).trans (eq_residual_iff_normal T S x φ hφ)

end TwoColor.LeastSquares
