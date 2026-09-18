import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive two-color densities and their covariance

The density simplex and covariance algebra in Sections 1.1, 1.2, and 7 of
`v8 two_color_exclusion_quenched_invariance.pdf`.
-/

noncomputable section

namespace TwoColor

set_option autoImplicit false

/-- A density vector in the open simplex, with vacancy, red, and blue components. -/
structure Density where
  vacancy : ℝ
  red : ℝ
  blue : ℝ
  vacancy_pos : 0 < vacancy
  red_pos : 0 < red
  blue_pos : 0 < blue
  sum_eq_one : vacancy + red + blue = 1

namespace Density

variable (ρ : Density)

/-- The total density of occupied sites. -/
def occupationDensity : ℝ := ρ.red + ρ.blue

/-- The fraction of red particles among occupied sites. -/
def colorFraction : ℝ := ρ.red / ρ.occupationDensity

/-- The coefficient of the color mode. -/
def colorVariance : ℝ :=
  ρ.occupationDensity * ρ.colorFraction * (1 - ρ.colorFraction)

theorem occupationDensity_pos : 0 < ρ.occupationDensity :=
  add_pos ρ.red_pos ρ.blue_pos

theorem occupationDensity_lt_one : ρ.occupationDensity < 1 := by
  unfold occupationDensity
  linarith [ρ.sum_eq_one, ρ.vacancy_pos]

theorem vacancy_eq_one_sub_occupationDensity :
    ρ.vacancy = 1 - ρ.occupationDensity := by
  unfold occupationDensity
  linarith [ρ.sum_eq_one]

theorem colorFraction_pos : 0 < ρ.colorFraction :=
  div_pos ρ.red_pos ρ.occupationDensity_pos

theorem colorFraction_lt_one : ρ.colorFraction < 1 := by
  apply (div_lt_one ρ.occupationDensity_pos).2
  unfold occupationDensity
  linarith [ρ.blue_pos]

theorem colorVariance_pos : 0 < ρ.colorVariance :=
  mul_pos (mul_pos ρ.occupationDensity_pos ρ.colorFraction_pos)
    (sub_pos.mpr ρ.colorFraction_lt_one)

theorem one_sub_colorFraction :
    1 - ρ.colorFraction = ρ.blue / ρ.occupationDensity := by
  unfold colorFraction
  apply (eq_div_iff (ne_of_gt ρ.occupationDensity_pos)).2
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt ρ.occupationDensity_pos)]
  unfold occupationDensity
  ring

theorem colorVariance_eq :
    ρ.colorVariance = ρ.red * ρ.blue / ρ.occupationDensity := by
  unfold colorVariance
  rw [ρ.one_sub_colorFraction]
  unfold colorFraction
  field_simp [ne_of_gt ρ.occupationDensity_pos]

/-- The covariance matrix of the red and blue one-site indicators. -/
def covariance : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ρ.red * (1 - ρ.red), -(ρ.red * ρ.blue);
     -(ρ.red * ρ.blue), ρ.blue * (1 - ρ.blue)]

@[simp] theorem covariance_zero_zero : ρ.covariance 0 0 = ρ.red * (1 - ρ.red) := rfl
@[simp] theorem covariance_zero_one : ρ.covariance 0 1 = -(ρ.red * ρ.blue) := rfl
@[simp] theorem covariance_one_zero : ρ.covariance 1 0 = -(ρ.red * ρ.blue) := rfl
@[simp] theorem covariance_one_one : ρ.covariance 1 1 = ρ.blue * (1 - ρ.blue) := rfl

theorem covariance_det :
    ρ.covariance.det = ρ.vacancy * ρ.red * ρ.blue := by
  rw [Matrix.det_fin_two]
  simp only [covariance_zero_zero, covariance_zero_one,
    covariance_one_zero, covariance_one_one]
  rw [ρ.vacancy_eq_one_sub_occupationDensity]
  unfold occupationDensity
  ring

theorem covariance_det_pos : 0 < ρ.covariance.det := by
  rw [ρ.covariance_det]
  exact mul_pos (mul_pos ρ.vacancy_pos ρ.red_pos) ρ.blue_pos

/-- The covariance quadratic form evaluated at the two color slopes. -/
def covarianceEnergy (p q : ℝ) : ℝ :=
  ρ.red * p ^ 2 + ρ.blue * q ^ 2 - (ρ.red * p + ρ.blue * q) ^ 2

theorem covarianceEnergy_eq_matrix (p q : ℝ) :
    ρ.covarianceEnergy p q =
      p * (ρ.covariance 0 0 * p + ρ.covariance 0 1 * q) +
      q * (ρ.covariance 1 0 * p + ρ.covariance 1 1 * q) := by
  simp only [covariance_zero_zero, covariance_zero_one,
    covariance_one_zero, covariance_one_one, covarianceEnergy]
  ring

theorem covarianceEnergy_decomposition (p q : ℝ) :
    ρ.covarianceEnergy p q =
      ρ.vacancy * (ρ.red * p ^ 2 + ρ.blue * q ^ 2) +
      ρ.red * ρ.blue * (p - q) ^ 2 := by
  rw [ρ.vacancy_eq_one_sub_occupationDensity]
  unfold covarianceEnergy occupationDensity
  ring

theorem covarianceEnergy_nonneg (p q : ℝ) : 0 ≤ ρ.covarianceEnergy p q := by
  rw [ρ.covarianceEnergy_decomposition]
  exact add_nonneg
    (mul_nonneg (le_of_lt ρ.vacancy_pos)
      (add_nonneg (mul_nonneg (le_of_lt ρ.red_pos) (sq_nonneg p))
        (mul_nonneg (le_of_lt ρ.blue_pos) (sq_nonneg q))))
    (mul_nonneg (le_of_lt (mul_pos ρ.red_pos ρ.blue_pos)) (sq_nonneg (p - q)))

theorem covarianceEnergy_pos_of_ne {p q : ℝ} (h : p ≠ 0 ∨ q ≠ 0) :
    0 < ρ.covarianceEnergy p q := by
  have hfirst : 0 < ρ.red * p ^ 2 + ρ.blue * q ^ 2 := by
    rcases h with hp | hq
    · exact add_pos_of_pos_of_nonneg (mul_pos ρ.red_pos (sq_pos_of_ne_zero hp))
        (mul_nonneg (le_of_lt ρ.blue_pos) (sq_nonneg q))
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (le_of_lt ρ.red_pos) (sq_nonneg p))
        (mul_pos ρ.blue_pos (sq_pos_of_ne_zero hq))
  rw [ρ.covarianceEnergy_decomposition]
  exact add_pos_of_pos_of_nonneg (mul_pos ρ.vacancy_pos hfirst)
    (mul_nonneg (le_of_lt (mul_pos ρ.red_pos ρ.blue_pos)) (sq_nonneg (p - q)))

theorem covarianceEnergy_pos {p q : ℝ} (h : (p, q) ≠ (0, 0)) :
    0 < ρ.covarianceEnergy p q := by
  apply ρ.covarianceEnergy_pos_of_ne
  by_cases hp : p = 0
  · right
    intro hq
    exact h (by simp [hp, hq])
  · exact Or.inl hp

theorem covarianceEnergy_eq_zero_iff (p q : ℝ) :
    ρ.covarianceEnergy p q = 0 ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro hz
    by_contra h
    have hne : p ≠ 0 ∨ q ≠ 0 := by
      by_cases hp : p = 0
      · exact Or.inr (fun hq => h ⟨hp, hq⟩)
      · exact Or.inl hp
    have := ρ.covarianceEnergy_pos_of_ne hne
    linarith
  · rintro ⟨rfl, rfl⟩
    simp [covarianceEnergy]

/-- Exact separation into occupation and color modes, as in Section 7. -/
theorem covarianceEnergy_occupation_color (p q : ℝ) :
    ρ.covarianceEnergy p q =
      ρ.occupationDensity * (1 - ρ.occupationDensity) *
        (ρ.colorFraction * p + (1 - ρ.colorFraction) * q) ^ 2 +
      ρ.colorVariance * (p - q) ^ 2 := by
  rw [ρ.colorVariance_eq, ρ.one_sub_colorFraction]
  unfold covarianceEnergy colorFraction occupationDensity
  have hr : ρ.red + ρ.blue ≠ 0 := ne_of_gt ρ.occupationDensity_pos
  field_simp
  ring

end Density

end TwoColor
