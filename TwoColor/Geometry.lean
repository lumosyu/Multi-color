import TwoColor.Model
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Outgoing lattice cells and affine functions

The finite sets in Section 1.1 are represented concretely: the base cube is
`{1, ..., L}^d`, the interior is `{2, ..., L - 1}^d`, and each bond has its
positive-coordinate orientation. The endpoint set includes the outgoing faces.
-/

noncomputable section

open scoped BigOperators

namespace TwoColor

/-- The base cube `Q_L = {1, ..., L}^d`. -/
def cube (d L : ℕ) : Finset (Site d) :=
  Fintype.piFinset (fun _ => Finset.Icc (1 : ℤ) (L : ℤ))

theorem cube_card (d L : ℕ) : (cube d L).card = L ^ d := by
  simp [cube, Fintype.card_piFinset]

/-- The interior support set `I_L = {2, ..., L - 1}^d`. -/
def interior (d L : ℕ) : Finset (Site d) :=
  Fintype.piFinset (fun _ => Finset.Icc (2 : ℤ) ((L : ℤ) - 1))

@[simp] theorem mem_cube {d L : ℕ} {x : Site d} :
    x ∈ cube d L ↔ ∀ j, 1 ≤ x j ∧ x j ≤ (L : ℤ) := by
  simp [cube]

@[simp] theorem mem_interior {d L : ℕ} {x : Site d} :
    x ∈ interior d L ↔ ∀ j, 2 ≤ x j ∧ x j ≤ (L : ℤ) - 1 := by
  simp [interior]

theorem interior_subset_cube (d L : ℕ) : interior d L ⊆ cube d L := by
  intro x hx
  apply mem_cube.mpr
  intro j
  have hj := mem_interior.mp hx j
  omega

/-- Add one in coordinate `j`. -/
def positiveStep {d : ℕ} (x : Site d) (j : Fin d) : Site d :=
  fun k => x k + if k = j then 1 else 0

@[simp] theorem positiveStep_same {d : ℕ} (x : Site d) (j : Fin d) :
    positiveStep x j j = x j + 1 := by
  simp [positiveStep]

theorem positiveStep_other {d : ℕ} (x : Site d) (j k : Fin d) (h : k ≠ j) :
    positiveStep x j k = x k := by
  simp [positiveStep, h]

theorem positiveStep_ne {d : ℕ} (x : Site d) (j : Fin d) :
    positiveStep x j ≠ x := by
  intro h
  have hj := congrFun h j
  simp only [positiveStep_same] at hj
  omega

theorem positiveStep_mem_cube_of_mem_interior {d L : ℕ} (x : Site d) (j : Fin d)
    (hx : x ∈ interior d L) : positiveStep x j ∈ cube d L := by
  apply mem_cube.mpr
  intro k
  have hk := mem_interior.mp hx k
  by_cases h : k = j
  · subst k
    simp only [positiveStep_same]
    omega
  · rw [positiveStep_other x j k h]
    omega

/-- Exactly one positive orientation of every outgoing bond based in the cube. -/
def outgoingBonds (d L : ℕ) : Finset (Site d × Site d) :=
  (cube d L).biUnion (fun x => Finset.univ.image (fun j : Fin d => (x, positiveStep x j)))

theorem mem_outgoingBonds {d L : ℕ} {e : Site d × Site d} :
    e ∈ outgoingBonds d L ↔ ∃ x ∈ cube d L, ∃ j : Fin d, (x, positiveStep x j) = e := by
  simp [outgoingBonds]

theorem outgoingBond_mem {d : ℕ} (L : ℕ) (x : Site d) (j : Fin d)
    (hx : x ∈ cube d L) : (x, positiveStep x j) ∈ outgoingBonds d L := by
  exact mem_outgoingBonds.mpr ⟨x, hx, j, rfl⟩

theorem outgoing_endpoints_ne {d L : ℕ} {e : Site d × Site d}
    (he : e ∈ outgoingBonds d L) : e.1 ≠ e.2 := by
  obtain ⟨x, _, j, rfl⟩ := mem_outgoingBonds.mp he
  exact (positiveStep_ne x j).symm

/-- The chosen positive orientation never includes the same bond in reverse. -/
theorem outgoing_reverse_not_mem {d L : ℕ} {e : Site d × Site d}
    (he : e ∈ outgoingBonds d L) : (e.2, e.1) ∉ outgoingBonds d L := by
  obtain ⟨x, _, j, rfl⟩ := mem_outgoingBonds.mp he
  intro hrev
  obtain ⟨y, _, k, h⟩ := mem_outgoingBonds.mp hrev
  have hy : y = positiveStep x j := congrArg Prod.fst h
  have hx : positiveStep y k = x := congrArg Prod.snd h
  rw [hy] at hx
  have hj := congrFun hx j
  by_cases hjk : j = k
  · simp [positiveStep, hjk] at hj
    omega
  · simp [positiveStep, hjk] at hj

/-- The full endpoint set `V_Q`, including outgoing faces. -/
def endpointSet (d L : ℕ) : Finset (Site d) :=
  (outgoingBonds d L).biUnion (fun e => {e.1, e.2})

theorem outgoing_left_mem_endpoint {d L : ℕ} {e : Site d × Site d}
    (he : e ∈ outgoingBonds d L) : e.1 ∈ endpointSet d L := by
  exact Finset.mem_biUnion.mpr ⟨e, he, by simp⟩

theorem outgoing_right_mem_endpoint {d L : ℕ} {e : Site d × Site d}
    (he : e ∈ outgoingBonds d L) : e.2 ∈ endpointSet d L := by
  exact Finset.mem_biUnion.mpr ⟨e, he, by simp⟩

theorem cube_subset_endpoint (d L : ℕ) (hd : 0 < d) :
    cube d L ⊆ endpointSet d L := by
  intro x hx
  exact outgoing_left_mem_endpoint (outgoingBond_mem L x ⟨0, hd⟩ hx)

theorem interior_subset_endpoint (d L : ℕ) (hd : 0 < d) :
    interior d L ⊆ endpointSet d L :=
  Finset.Subset.trans (interior_subset_cube d L) (cube_subset_endpoint d L hd)

theorem cube_nonempty (d L : ℕ) (hL : 0 < L) : (cube d L).Nonempty := by
  refine ⟨fun _ => 1, mem_cube.mpr ?_⟩
  intro j
  constructor
  · exact le_rfl
  · exact_mod_cast hL

theorem cube_card_pos (d L : ℕ) (hL : 0 < L) : 0 < (cube d L).card :=
  Finset.card_pos.mpr (cube_nonempty d L hL)

theorem endpointSet_nonempty (d L : ℕ) (hd : 0 < d) (hL : 0 < L) :
    (endpointSet d L).Nonempty :=
  (cube_nonempty d L hL).mono (cube_subset_endpoint d L hd)

/-- The Euclidean pairing of an integer site with a real slope. -/
def dot {d : ℕ} (x : Site d) (p : Fin d → ℝ) : ℝ :=
  ∑ j, (x j : ℝ) * p j

theorem dot_positiveStep {d : ℕ} (x : Site d) (j : Fin d) (p : Fin d → ℝ) :
    dot (positiveStep x j) p = dot x p + p j := by
  simp [dot, positiveStep, add_mul, Finset.sum_add_distrib]

/-- A finite species-linear observable with spatial coefficient `a`. -/
def linearStatistic {V : Type*} (S : Finset V) (a : V → ℝ) (i : Color)
    (η : Config V) : ℝ :=
  ∑ z ∈ S, a z * indicator i η z

theorem exchangeDiff_linearStatistic {V : Type*} [DecidableEq V]
    (S : Finset V) (a : V → ℝ) (i : Color) (η : Config V) (x y : V)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    exchangeDiff (linearStatistic S a i) x y η =
      (a y - a x) * (indicator i η x - indicator i η y) := by
  let g : V → ℝ := fun z =>
    a z * indicator i (exchange η x y) z - a z * indicator i η z
  have hsub : ({x, y} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hsum : ∑ z ∈ S, g z = ∑ z ∈ ({x, y} : Finset V), g z := by
    symm
    apply Finset.sum_subset hsub
    intro z _ hz
    have hzx : z ≠ x := by
      intro h
      exact hz (by simp [h])
    have hzy : z ≠ y := by
      intro h
      exact hz (by simp [h])
    simp [g, indicator, exchange_apply_of_ne η x y z hzx hzy]
  unfold exchangeDiff linearStatistic
  rw [← Finset.sum_sub_distrib]
  change (∑ z ∈ S, g z) = _
  rw [hsum]
  simp [g, hxy]
  ring

/-- The affine source on a finite endpoint set, with the two color slopes explicit. -/
def affine {d : ℕ} (S : Finset (Site d)) (pRed pBlue : Fin d → ℝ)
    (η : Config (Site d)) : ℝ :=
  linearStatistic S (fun z => dot z pRed) 1 η +
    linearStatistic S (fun z => dot z pBlue) 2 η

theorem exchangeDiff_affine {d : ℕ} (S : Finset (Site d))
    (pRed pBlue : Fin d → ℝ) (η : Config (Site d)) (x y : Site d)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    exchangeDiff (affine S pRed pBlue) x y η =
      (dot y pRed - dot x pRed) * (indicator 1 η x - indicator 1 η y) +
        (dot y pBlue - dot x pBlue) * (indicator 2 η x - indicator 2 η y) := by
  unfold exchangeDiff affine
  rw [add_sub_add_comm]
  exact congrArg₂ (fun a b : ℝ => a + b)
    (exchangeDiff_linearStatistic S (fun z => dot z pRed) 1 η x y hx hy hxy)
    (exchangeDiff_linearStatistic S (fun z => dot z pBlue) 2 η x y hx hy hxy)

/-- The paper's `ℓ_{Q,p}`, summed over the full outgoing endpoint set. -/
def cellAffine (d L : ℕ) (pRed pBlue : Fin d → ℝ) : Config (Site d) → ℝ :=
  affine (endpointSet d L) pRed pBlue

/-- The affine gradient has the sign and normalization used in equations (1.1) and (1.3). -/
theorem exchangeDiff_cellAffine {d L : ℕ} (pRed pBlue : Fin d → ℝ)
    (η : Config (Site d)) (x : Site d) (j : Fin d) (hx : x ∈ cube d L) :
    exchangeDiff (cellAffine d L pRed pBlue) x (positiveStep x j) η =
      pRed j * (indicator 1 η x - indicator 1 η (positiveStep x j)) +
        pBlue j * (indicator 2 η x - indicator 2 η (positiveStep x j)) := by
  have he := outgoingBond_mem L x j hx
  rw [cellAffine, exchangeDiff_affine _ _ _ _ _ _
    (outgoing_left_mem_endpoint he) (outgoing_right_mem_endpoint he)
    (positiveStep_ne x j).symm]
  simp [dot_positiveStep]

end TwoColor
