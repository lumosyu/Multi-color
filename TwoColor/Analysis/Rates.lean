import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar estimates for the quenched argument

These are unconditional real-analysis lemmas used in Section 9 of
`v8 two_color_exclusion_quenched_invariance.pdf`. They do not construct the
exclusion process or assert either main theorem of the paper.

The summability statements use `n + 1` to index the paper's series over positive
integers. In particular, they make no convention-dependent claim about `0 ^ p`.
-/

namespace TwoColor

/-- The resolvent exponent in Proposition 9.2. -/
noncomputable def quenchedExponent (α : ℝ) : ℝ := α / (2 * α + 3)

theorem rate_denominator_pos {α : ℝ} (hα : 0 < α) : 0 < 2 * α + 3 := by
  linarith

theorem quenchedExponent_pos {α : ℝ} (hα : 0 < α) : 0 < quenchedExponent α :=
  div_pos hα (rate_denominator_pos hα)

theorem quenchedExponent_lt_half {α : ℝ} (hα : 0 < α) :
    quenchedExponent α < 1 / 2 := by
  unfold quenchedExponent
  apply (div_lt_iff₀ (rate_denominator_pos hα)).2
  linarith

/-- The two powers of `λ` agree at the real balancing scale in Proposition 9.2.
This is the exponent calculation, not the integer rounding argument for `L`. -/
theorem corrector_exponent_balance {α : ℝ} (hα : 0 < α) :
    1 - (α + 3) / (2 * α + 3) = quenchedExponent α := by
  unfold quenchedExponent
  field_simp [ne_of_gt (rate_denominator_pos hα)]
  ring

/-- The energy term at the positive real balancing scale from Proposition 9.2. -/
theorem corrector_real_scale_energy (α : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (lam ^ (-1 / (2 * α + 3))) ^ (-α) = lam ^ quenchedExponent α := by
  rw [← Real.rpow_mul hlam.le]
  congr 1
  unfold quenchedExponent
  ring

/-- The massive norm term at the same real scale. No integer rounding is asserted. -/
theorem corrector_real_scale_mass {α lam : ℝ} (hα : 0 < α) (hlam : 0 < lam) :
    lam * (lam ^ (-1 / (2 * α + 3))) ^ (α + 3) = lam ^ quenchedExponent α := by
  calc
    lam * (lam ^ (-1 / (2 * α + 3))) ^ (α + 3) =
        lam ^ (1 : ℝ) * lam ^ ((-1 / (2 * α + 3)) * (α + 3)) := by
      rw [Real.rpow_one, Real.rpow_mul hlam.le]
    _ = lam ^ (1 + (-1 / (2 * α + 3)) * (α + 3)) :=
      (Real.rpow_add hlam _ _).symm
    _ = lam ^ quenchedExponent α := by
      congr 1
      calc
        1 + (-1 / (2 * α + 3)) * (α + 3) =
            1 - (α + 3) / (2 * α + 3) := by ring
        _ = quenchedExponent α := corrector_exponent_balance hα

/-- Exact value of the two-term corrector bound at its balancing scale. -/
theorem corrector_real_scale_sum {α lam : ℝ} (hα : 0 < α) (hlam : 0 < lam) :
    (lam ^ (-1 / (2 * α + 3))) ^ (-α) +
      lam * (lam ^ (-1 / (2 * α + 3))) ^ (α + 3) =
        2 * lam ^ quenchedExponent α := by
  rw [corrector_real_scale_energy α hlam, corrector_real_scale_mass hα hlam]
  ring

/-- The power in the Maxwell--Woodroofe majorant from Lemma 9.5. -/
theorem maxwellWoodroofe_exponent (β : ℝ) :
    -(3 : ℝ) / 2 + (1 - β) / 2 = -1 - β / 2 := by
  ring

/-- A scalar form of the estimate used in Proposition 9.3. -/
theorem square_le_two_mul_div_one_add {a u : ℝ}
    (hu : 0 ≤ u) (ha : 0 ≤ a) (hau : a ≤ u) (ha1 : a ≤ 1) :
    a ^ 2 ≤ 2 * u / (1 + u) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 + u)).2
  rcases le_total u 1 with hu1 | h1u
  · have hsq : a ^ 2 ≤ u ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self ha hau
    have hu_sq : u ^ 2 ≤ u := by nlinarith
    calc
      a ^ 2 * (1 + u) ≤ a ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg a)
      _ ≤ 2 * u := by nlinarith
  · have hsq : a ^ 2 ≤ 1 := by
      simpa only [pow_two, mul_one] using mul_self_le_mul_self ha ha1
    calc
      a ^ 2 * (1 + u) ≤ 1 * (1 + u) :=
        mul_le_mul_of_nonneg_right hsq (by linarith)
      _ ≤ 2 * u := by linarith

/-- The elementary spectral-kernel estimate in Proposition 9.3, before
integrating against the drift's spectral measure. -/
theorem one_sub_exp_neg_sq_le {u : ℝ} (hu : 0 ≤ u) :
    (1 - Real.exp (-u)) ^ 2 ≤ 2 * u / (1 + u) := by
  apply square_le_two_mul_div_one_add hu
  · have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
    linarith
  · have h := Real.add_one_le_exp (-u)
    linarith
  · have h := Real.exp_pos (-u)
    linarith

/-- Pointwise comparison of the conditional-mean spectral kernel with the
resolvent kernel in (9.23). This statement performs no spectral integration. -/
theorem conditional_mean_kernel_le {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) :
    (1 - Real.exp (-(t * s))) ^ 2 / s ^ 2 ≤ 2 * t / (s * (1 + t * s)) := by
  have hts : 0 ≤ t * s := mul_nonneg ht hs.le
  have hden : 0 < 1 + t * s := by linarith
  calc
    (1 - Real.exp (-(t * s))) ^ 2 / s ^ 2 ≤
        (2 * (t * s) / (1 + t * s)) / s ^ 2 :=
      div_le_div_of_nonneg_right (one_sub_exp_neg_sq_le hts) (sq_nonneg s)
    _ = 2 * t / (s * (1 + t * s)) := by
      field_simp [ne_of_gt hs, ne_of_gt hden]

/-- Combining the two real powers in a Maxwell--Woodroofe summand. -/
theorem maxwellWoodroofe_weight_eq {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t ^ (-(3 : ℝ) / 2) * t ^ ((1 - β) / 2) = t ^ (-1 - β / 2) := by
  rw [← Real.rpow_add ht, maxwellWoodroofe_exponent]

/-- The positive-integer `p`-series which majorizes the series in (9.25). -/
theorem summable_maxwellWoodroofe_majorant {β : ℝ} (hβ : 0 < β) (C : ℝ) :
    Summable (fun n : ℕ =>
      C * ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2) * ((n : ℝ) + 1) ^ ((1 - β) / 2)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - β / 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hs' : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-1 - β / 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  convert Summable.mul_left C hs' using 1
  funext n
  rw [mul_assoc, maxwellWoodroofe_weight_eq (by positivity : 0 < (n : ℝ) + 1)]

/-- A nonnegative scalar sequence with the conditional-mean growth bound of
Lemma 9.5 satisfies the scalar Maxwell--Woodroofe series condition.

Here `f n` represents the norm at the positive time `n + 1`; deriving that
growth bound for the actual tagged process is a separate, unformalized step. -/
theorem summable_maxwellWoodroofe_of_power_bound {β C : ℝ} {f : ℕ → ℝ}
    (hβ : 0 < β) (hf : ∀ n, 0 ≤ f n)
    (hbound : ∀ n, f n ≤ C * ((n : ℝ) + 1) ^ ((1 - β) / 2)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2) * f n) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (hf n))
    (fun n => ?_) (summable_maxwellWoodroofe_majorant hβ C)
  calc
    ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2) * f n ≤
        ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2) *
          (C * ((n : ℝ) + 1) ^ ((1 - β) / 2)) :=
      mul_le_mul_of_nonneg_left (hbound n) (Real.rpow_nonneg (by positivity) _)
    _ = C * ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2) *
        ((n : ℝ) + 1) ^ ((1 - β) / 2) := by ring

end TwoColor
