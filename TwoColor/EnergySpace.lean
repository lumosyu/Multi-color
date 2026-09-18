import TwoColor.FiniteVolume
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The finite bond-energy Hilbert space

The exchange gradient is weighted by the square root of its product-equilibrium
probability and its jump rate. For nonnegative stirring rates, its squared
Euclidean norm is exactly the existing finite-volume energy. This includes
the degenerate physical rate `δ = 0`; no coercivity assumption is imposed.
-/

noncomputable section

open scoped BigOperators

namespace TwoColor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One coordinate per supplied bond and finite configuration. -/
abbrev BondState (E : Finset (V × V)) := E × Config V

abbrev BondSpace (E : Finset (V × V)) := EuclideanSpace ℝ (BondState E)

/-- The space of corrections depending only on the specified interior. -/
def correctionSpace (I : Finset V) : Submodule ℝ (Config V → ℝ) where
  carrier := {φ | DependsOnlyOn I φ}
  zero_mem' := dependsOnlyOn_const I 0
  add_mem' := by
    intro φ ψ hφ hψ η ζ h
    exact congrArg₂ (· + ·) (hφ η ζ h) (hψ η ζ h)
  smul_mem' := by
    intro c φ hφ η ζ h
    exact congrArg (fun a : ℝ => c * a) (hφ η ζ h)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_correctionSpace (I : Finset V) (φ : Config V → ℝ) :
    φ ∈ correctionSpace I ↔ DependsOnlyOn I φ := Iff.rfl

/-- The exchange-gradient map in finite equilibrium-weighted coordinates. -/
def weightedGradient (ρ : Density) (E : Finset (V × V)) (δ : ℝ) :
    (Config V → ℝ) →ₗ[ℝ] BondSpace E where
  toFun F := WithLp.toLp 2 (fun z : BondState E =>
    Real.sqrt (configWeight ρ z.2 * rate δ z.2 z.1.val.1 z.1.val.2) *
      exchangeDiff F z.1.val.1 z.1.val.2 z.2)
  map_add' F G := by
    ext z
    change _ * ((F + G) _ - (F + G) _) =
      _ * (F _ - F _) + _ * (G _ - G _)
    simp only [Pi.add_apply]
    ring
  map_smul' c F := by
    ext z
    change _ * ((c • F) _ - (c • F) _) = c * (_ * (F _ - F _))
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

@[simp] theorem weightedGradient_apply (ρ : Density) (E : Finset (V × V)) (δ : ℝ)
    (F : Config V → ℝ) (z : BondState E) :
    weightedGradient ρ E δ F z =
      Real.sqrt (configWeight ρ z.2 * rate δ z.2 z.1.val.1 z.1.val.2) *
        exchangeDiff F z.1.val.1 z.1.val.2 z.2 := rfl

/-- The inner product is precisely the paper's bilinear energy. -/
theorem weightedGradient_inner (ρ : Density) (E : Finset (V × V))
    {δ : ℝ} (hδ : 0 ≤ δ) (F G : Config V → ℝ) :
    inner ℝ (weightedGradient ρ E δ F) (weightedGradient ρ E δ G) =
      energyForm ρ E δ F G := by
  simp only [PiLp.inner_apply, weightedGradient_apply]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ e : E, ∑ η : Config V, configWeight ρ η *
        (rate δ η e.val.1 e.val.2 * exchangeDiff F e.val.1 e.val.2 η *
          exchangeDiff G e.val.1 e.val.2 η) := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro η _
      have hw : 0 ≤ configWeight ρ η * rate δ η e.val.1 e.val.2 :=
        mul_nonneg (configWeight_pos ρ η).le (rate_nonneg δ η e.val.1 e.val.2 hδ)
      change (Real.sqrt (configWeight ρ η * rate δ η e.val.1 e.val.2) *
          exchangeDiff G e.val.1 e.val.2 η) *
        (Real.sqrt (configWeight ρ η * rate δ η e.val.1 e.val.2) *
          exchangeDiff F e.val.1 e.val.2 η) = _
      calc
        _ = (Real.sqrt (configWeight ρ η * rate δ η e.val.1 e.val.2)) ^ 2 *
            exchangeDiff F e.val.1 e.val.2 η * exchangeDiff G e.val.1 e.val.2 η := by ring
        _ = _ := by rw [Real.sq_sqrt hw]; ring
    _ = _ := Finset.sum_coe_sort E (fun e => expectation ρ
      (fun η => rate δ η e.1 e.2 * exchangeDiff F e.1 e.2 η * exchangeDiff G e.1 e.2 η))

/-- The original finite energy is a squared norm, even when the rate vanishes. -/
theorem weightedGradient_norm_sq (ρ : Density) (E : Finset (V × V))
    {δ : ℝ} (hδ : 0 ≤ δ) (F : Config V → ℝ) :
    ‖weightedGradient ρ E δ F‖ ^ 2 = energy ρ E δ F := by
  rw [← real_inner_self_eq_norm_sq, weightedGradient_inner ρ E hδ]
  rfl

end TwoColor
