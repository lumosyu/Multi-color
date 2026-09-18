import Mathlib

/-! A setup check using the exponent from the two-color exclusion paper.
This verifies the installation, not the main theorems of the paper. -/

namespace MultiColorLean

theorem paper_beta_bounds (α : ℝ) (hα : 0 < α) :
    0 < α / (2 * α + 3) ∧ α / (2 * α + 3) < (1 / 2 : ℝ) := by
  have hd : 0 < 2 * α + 3 := by linarith
  constructor
  · exact div_pos hα hd
  · apply (div_lt_iff₀ hd).2
    linarith

#print axioms paper_beta_bounds

end MultiColorLean
