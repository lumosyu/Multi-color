import TwoColor

/-! Compatibility entry point for the original installation check. -/

namespace MultiColorLean

theorem paper_beta_bounds (α : ℝ) (hα : 0 < α) :
    0 < α / (2 * α + 3) ∧ α / (2 * α + 3) < (1 / 2 : ℝ) :=
  ⟨TwoColor.quenchedExponent_pos hα, TwoColor.quenchedExponent_lt_half hα⟩

end MultiColorLean
