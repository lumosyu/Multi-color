import TwoColor.FiniteVolume
import TwoColor.Geometry

/-!
# The concrete outgoing scalar Dirichlet cell problem

This module specializes the finite variational energy to the endpoint set,
outgoing bonds, interior, and affine source of equation (1.1). The result is a
scalar variational definition with the paper's division by the number of base
vertices. No existence of a minimizing correction, matrix representation, or
infinite-volume convergence is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace TwoColor

set_option autoImplicit false

/-- The finite endpoint configuration space of the outgoing side-`L` cube. -/
abbrev CellSite (d L : ℕ) := ↥(endpointSet d L)

/-- Outgoing bonds, now with their endpoints in the finite cell site type. -/
def cellBonds (d L : ℕ) : Finset (CellSite d L × CellSite d L) := by
  classical
  exact Finset.univ.filter (fun e => (e.1.val, e.2.val) ∈ outgoingBonds d L)

/-- The Dirichlet interior, as a subset of the finite endpoint site type. -/
def cellInterior (d L : ℕ) : Finset (CellSite d L) := by
  classical
  exact Finset.univ.filter (fun x => x.val ∈ interior d L)

@[simp] theorem mem_cellBonds {d L : ℕ} (e : CellSite d L × CellSite d L) :
    e ∈ cellBonds d L ↔ (e.1.val, e.2.val) ∈ outgoingBonds d L := by
  classical
  simp [cellBonds]

theorem cellBond_endpoints_ne {d L : ℕ} {e : CellSite d L × CellSite d L}
    (he : e ∈ cellBonds d L) : e.1 ≠ e.2 := by
  intro h
  exact outgoing_endpoints_ne ((mem_cellBonds e).mp he) (congrArg Subtype.val h)

/-- Every physical bond occurs with at most one orientation in the finite generator. -/
theorem cellBonds_reverse_not_mem {d L : ℕ} {e : CellSite d L × CellSite d L}
    (he : e ∈ cellBonds d L) : (e.2, e.1) ∉ cellBonds d L := by
  intro hrev
  exact outgoing_reverse_not_mem ((mem_cellBonds e).mp he)
    ((mem_cellBonds (e.2, e.1)).mp hrev)

@[simp] theorem mem_cellInterior {d L : ℕ} (x : CellSite d L) :
    x ∈ cellInterior d L ↔ x.val ∈ interior d L := by
  classical
  simp [cellInterior]

/-- Interior measurability is exactly dependence on the labels in `I_Q`. -/
theorem dependsOnlyOn_cellInterior_iff {d L : ℕ} (φ : Config (CellSite d L) → ℝ) :
    DependsOnlyOn (cellInterior d L) φ ↔
      ∀ η ζ, (∀ x : CellSite d L, x.val ∈ interior d L → η x = ζ x) → φ η = φ ζ := by
  simp only [DependsOnlyOn, mem_cellInterior]

/-- The paper's affine source, summed over precisely the outgoing endpoints. -/
def cellAffineSource (d L : ℕ) (pRed pBlue : Fin d → ℝ)
    (η : Config (CellSite d L)) : ℝ :=
  ∑ x : CellSite d L,
    (dot x.val pRed * indicator 1 η x + dot x.val pBlue * indicator 2 η x)

/-- Restricting a lattice configuration gives exactly the paper's affine source. -/
theorem cellAffineSource_restrict (d L : ℕ) (pRed pBlue : Fin d → ℝ)
    (η : Config (Site d)) :
    cellAffineSource d L pRed pBlue (fun x => η x.val) = cellAffine d L pRed pBlue η := by
  classical
  simp only [cellAffineSource, cellAffine, affine, linearStatistic, Finset.sum_add_distrib]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · exact Finset.sum_coe_sort (endpointSet d L) (fun x => dot x pRed * indicator 1 η x)
  · exact Finset.sum_coe_sort (endpointSet d L) (fun x => dot x pBlue * indicator 2 η x)

/-- The number of base vertices, viewed as a real normalization factor. -/
def cellVolume (d L : ℕ) : ℝ := (cube d L).card

theorem cellVolume_eq (d L : ℕ) : cellVolume d L = (L : ℝ) ^ d := by
  simp only [cellVolume, cube_card, Nat.cast_pow]

theorem cellVolume_nonneg (d L : ℕ) : 0 ≤ cellVolume d L := by
  exact Nat.cast_nonneg _

theorem cellVolume_pos (d L : ℕ) (hL : 0 < L) : 0 < cellVolume d L := by
  unfold cellVolume
  exact_mod_cast (Finset.card_pos.mpr (cube_nonempty d L hL))

/-- The scalar quantity defined by the right-hand side of equation (1.1).

The slopes are not covariance-normalized. A later matrix construction can
identify this quantity with `p · A_Q^δ p`.
-/
def dirichletCellEnergy (ρ : Density) (d L : ℕ) (δ : ℝ)
    (pRed pBlue : Fin d → ℝ) : ℝ :=
  primalEnergy ρ (cellBonds d L) (cellInterior d L) δ
    (cellAffineSource d L pRed pBlue) / cellVolume d L

/-- Energy density of an individual finite-cell correction. -/
def cellCompetitorEnergy (ρ : Density) (d L : ℕ) (δ : ℝ)
    (pRed pBlue : Fin d → ℝ) (φ : Config (CellSite d L) → ℝ) : ℝ :=
  energy ρ (cellBonds d L) δ
    (fun η => cellAffineSource d L pRed pBlue η + φ η) / cellVolume d L

theorem dirichletCellEnergy_nonneg (ρ : Density) (d L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (pRed pBlue : Fin d → ℝ) : 0 ≤ dirichletCellEnergy ρ d L δ pRed pBlue := by
  exact div_nonneg (primalEnergy_nonneg ρ _ _ hδ _) (cellVolume_nonneg d L)

theorem dirichletCellEnergy_le_competitor (ρ : Density) (d L : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (pRed pBlue : Fin d → ℝ)
    (φ : Config (CellSite d L) → ℝ) (hφ : DependsOnlyOn (cellInterior d L) φ) :
    dirichletCellEnergy ρ d L δ pRed pBlue ≤
      cellCompetitorEnergy ρ d L δ pRed pBlue φ := by
  exact div_le_div_of_nonneg_right (primalEnergy_le_competitor ρ _ _ hδ _ φ hφ)
    (cellVolume_nonneg d L)

theorem dirichletCellEnergy_le_affine (ρ : Density) (d L : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (pRed pBlue : Fin d → ℝ) :
    dirichletCellEnergy ρ d L δ pRed pBlue ≤
      energy ρ (cellBonds d L) δ (cellAffineSource d L pRed pBlue) / cellVolume d L := by
  exact div_le_div_of_nonneg_right (primalEnergy_le_affine ρ _ _ hδ _)
    (cellVolume_nonneg d L)

theorem dirichletCellEnergy_mono (ρ : Density) (d L : ℕ)
    {ε δ : ℝ} (hε : 0 ≤ ε) (h : ε ≤ δ) (pRed pBlue : Fin d → ℝ) :
    dirichletCellEnergy ρ d L ε pRed pBlue ≤ dirichletCellEnergy ρ d L δ pRed pBlue := by
  exact div_le_div_of_nonneg_right (primalEnergy_mono ρ _ _ hε h _)
    (cellVolume_nonneg d L)

end TwoColor
