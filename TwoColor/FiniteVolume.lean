import TwoColor.Model
import TwoColor.Density
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring

/-!
# Finite-volume equilibrium, generator, and variational energy

The finite product equilibrium and bond energies of Section 1.1 are implemented
as finite real sums. The normalization theorem verifies that these sums are
expectations under a probability distribution. The integration-by-parts theorem
records the paper's factor of two in its Dirichlet-form convention.

An edge is represented by a pair of endpoints; a physical application supplies
exactly one orientation of each unoriented bond. This module permits an arbitrary
finite edge set and does not yet identify the outgoing lattice cubes.
-/

noncomputable section

open scoped BigOperators

namespace TwoColor

/-- One-site probabilities, in vacancy/red/blue order. -/
def Density.colorWeight (ρ : Density) (i : Color) : ℝ :=
  if i = 0 then ρ.vacancy else if i = 1 then ρ.red else ρ.blue

theorem Density.colorWeight_pos (ρ : Density) (i : Color) : 0 < ρ.colorWeight i := by
  unfold Density.colorWeight
  split
  · exact ρ.vacancy_pos
  · split
    · exact ρ.red_pos
    · exact ρ.blue_pos

theorem Density.sum_colorWeight (ρ : Density) : ∑ i : Color, ρ.colorWeight i = 1 := by
  simpa [Density.colorWeight, Fin.sum_univ_succ, add_assoc] using ρ.sum_eq_one

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The probability of a finite configuration under the product equilibrium. -/
def configWeight (ρ : Density) (η : Config V) : ℝ :=
  ∏ x, ρ.colorWeight (η x)

omit [DecidableEq V] in
theorem configWeight_pos (ρ : Density) (η : Config V) : 0 < configWeight ρ η := by
  exact Finset.prod_pos (fun x _ => ρ.colorWeight_pos (η x))

theorem sum_configWeight (ρ : Density) : ∑ η : Config V, configWeight ρ η = 1 := by
  calc
    _ = ∏ _x : V, ∑ i : Color, ρ.colorWeight i :=
      (Fintype.prod_sum (fun (_x : V) (i : Color) => ρ.colorWeight i)).symm
    _ = 1 := by simp [Density.sum_colorWeight]

/-- Expectation under the finite product equilibrium. -/
def expectation (ρ : Density) (F : Config V → ℝ) : ℝ :=
  ∑ η, configWeight ρ η * F η

@[simp] theorem expectation_const (ρ : Density) (c : ℝ) :
    expectation ρ (fun _ : Config V => c) = c := by
  rw [expectation, ← Finset.sum_mul, sum_configWeight, one_mul]

theorem expectation_nonneg (ρ : Density) (F : Config V → ℝ) (hF : ∀ η, 0 ≤ F η) :
    0 ≤ expectation ρ F := by
  exact Finset.sum_nonneg (fun η _ => mul_nonneg (configWeight_pos ρ η).le (hF η))

theorem expectation_mono (ρ : Density) {F G : Config V → ℝ} (h : ∀ η, F η ≤ G η) :
    expectation ρ F ≤ expectation ρ G := by
  exact Finset.sum_le_sum (fun η _ => mul_le_mul_of_nonneg_left (h η) (configWeight_pos ρ η).le)

theorem expectation_add (ρ : Density) (F G : Config V → ℝ) :
    expectation ρ (fun η => F η + G η) = expectation ρ F + expectation ρ G := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (ρ : Density) (F G : Config V → ℝ) :
    expectation ρ (fun η => F η - G η) = expectation ρ F - expectation ρ G := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem expectation_neg (ρ : Density) (F : Config V → ℝ) :
    expectation ρ (fun η => -F η) = -expectation ρ F := by
  simp [expectation, Finset.sum_neg_distrib]

theorem expectation_mul_const (ρ : Density) (F : Config V → ℝ) (c : ℝ) :
    expectation ρ (fun η => F η * c) = expectation ρ F * c := by
  simp [expectation, ← mul_assoc, Finset.sum_mul]

theorem expectation_finset_sum (ρ : Density) {ι : Type*} (s : Finset ι)
    (F : ι → Config V → ℝ) :
    expectation ρ (fun η => ∑ i ∈ s, F i η) = ∑ i ∈ s, expectation ρ (F i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- The involution of configuration space induced by exchanging two sites. -/
def exchangeEquiv (x y : V) : Config V ≃ Config V where
  toFun η := exchange η x y
  invFun η := exchange η x y
  left_inv η := exchange_exchange η x y
  right_inv η := exchange_exchange η x y

theorem configWeight_exchange (ρ : Density) (η : Config V) (x y : V) :
    configWeight ρ (exchange η x y) = configWeight ρ η := by
  exact Equiv.prod_comp (Equiv.swap x y) (fun z => ρ.colorWeight (η z))

theorem expectation_exchange (ρ : Density) (F : Config V → ℝ) (x y : V) :
    expectation ρ (fun η => F (exchange η x y)) = expectation ρ F := by
  unfold expectation
  calc
    _ = ∑ η : Config V, configWeight ρ (exchange η x y) * F (exchange η x y) := by
      apply Finset.sum_congr rfl
      intro η _
      rw [configWeight_exchange]
    _ = _ := (exchangeEquiv x y).sum_comp (fun η => configWeight ρ η * F η)

/-- Finite generator, with one term for each supplied bond. -/
def generator (E : Finset (V × V)) (δ : ℝ) (F : Config V → ℝ) (η : Config V) : ℝ :=
  ∑ e ∈ E, rate δ η e.1 e.2 * exchangeDiff F e.1 e.2 η

/-- The paper's bilinear energy, twice the usual Dirichlet form. -/
def energyForm (ρ : Density) (E : Finset (V × V)) (δ : ℝ)
    (F G : Config V → ℝ) : ℝ :=
  ∑ e ∈ E, expectation ρ (fun η =>
    rate δ η e.1 e.2 * exchangeDiff F e.1 e.2 η * exchangeDiff G e.1 e.2 η)

def energy (ρ : Density) (E : Finset (V × V)) (δ : ℝ) (F : Config V → ℝ) : ℝ :=
  energyForm ρ E δ F F

theorem energy_eq_sum_sq (ρ : Density) (E : Finset (V × V)) (δ : ℝ)
    (F : Config V → ℝ) :
    energy ρ E δ F = ∑ e ∈ E, expectation ρ (fun η =>
      rate δ η e.1 e.2 * (exchangeDiff F e.1 e.2 η) ^ 2) := by
  simp [energy, energyForm, pow_two, mul_assoc]

theorem energy_nonneg (ρ : Density) (E : Finset (V × V)) {δ : ℝ} (hδ : 0 ≤ δ)
    (F : Config V → ℝ) : 0 ≤ energy ρ E δ F := by
  rw [energy_eq_sum_sq]
  exact Finset.sum_nonneg (fun e _ => expectation_nonneg ρ _ (fun η =>
    mul_nonneg (rate_nonneg δ η e.1 e.2 hδ) (sq_nonneg _)))

theorem energy_mono (ρ : Density) (E : Finset (V × V)) {ε δ : ℝ} (h : ε ≤ δ)
    (F : Config V → ℝ) : energy ρ E ε F ≤ energy ρ E δ F := by
  rw [energy_eq_sum_sq, energy_eq_sum_sq]
  exact Finset.sum_le_sum (fun e _ => expectation_mono ρ (fun η =>
    mul_le_mul_of_nonneg_right (rate_mono ε δ η e.1 e.2 h) (sq_nonneg _)))

theorem energyForm_symm (ρ : Density) (E : Finset (V × V)) (δ : ℝ)
    (F G : Config V → ℝ) : energyForm ρ E δ F G = energyForm ρ E δ G F := by
  unfold energyForm
  congr 1
  funext e
  congr 1
  funext η
  ring

theorem bond_integration_by_parts (ρ : Density) (δ : ℝ) (F G : Config V → ℝ) (x y : V) :
    expectation ρ (fun η => rate δ η x y * exchangeDiff F x y η * exchangeDiff G x y η) =
      -2 * expectation ρ (fun η => F η * rate δ η x y * exchangeDiff G x y η) := by
  have h := expectation_exchange ρ
    (fun η => F (exchange η x y) * rate δ η x y * exchangeDiff G x y η) x y
  simp only [exchange_exchange, rate_exchange, exchangeDiff_exchange, mul_neg,
    expectation_neg] at h
  calc
    _ = expectation ρ (fun η =>
        (F (exchange η x y) * rate δ η x y * exchangeDiff G x y η) -
        (F η * rate δ η x y * exchangeDiff G x y η)) := by
      congr 1
      funext η
      unfold exchangeDiff
      ring
    _ = _ := by rw [expectation_sub, ← h]; ring

/-- The factor two identity stated at the beginning of Section 2.1. -/
theorem energyForm_eq_neg_generator (ρ : Density) (E : Finset (V × V)) (δ : ℝ)
    (F G : Config V → ℝ) :
    energyForm ρ E δ F G = 2 * expectation ρ (fun η => F η * (-generator E δ G η)) := by
  unfold energyForm
  simp_rw [bond_integration_by_parts]
  calc
    _ = -2 * expectation ρ (fun η =>
        ∑ e ∈ E, F η * rate δ η e.1 e.2 * exchangeDiff G e.1 e.2 η) := by
      rw [expectation_finset_sum, Finset.mul_sum]
    _ = _ := by
      have hfun : (fun η => ∑ e ∈ E,
          F η * rate δ η e.1 e.2 * exchangeDiff G e.1 e.2 η) =
          (fun η => F η * generator E δ G η) := by
        funext η
        simp [generator, Finset.mul_sum, mul_assoc]
      rw [hfun]
      simp only [mul_neg, expectation_neg]
      ring

/-- The finite product equilibrium annihilates the generator. -/
theorem expectation_generator (ρ : Density) (E : Finset (V × V)) (δ : ℝ)
    (F : Config V → ℝ) : expectation ρ (generator E δ F) = 0 := by
  have h := energyForm_eq_neg_generator ρ E δ (fun _ => 1) F
  simp [energyForm, exchangeDiff_const, expectation_neg] at h
  exact h

/-- Reversibility of the finite generator under product equilibrium. -/
theorem generator_reversible (ρ : Density) (E : Finset (V × V)) (δ : ℝ)
    (F G : Config V → ℝ) :
    expectation ρ (fun η => F η * generator E δ G η) =
      expectation ρ (fun η => G η * generator E δ F η) := by
  have h := energyForm_symm ρ E δ F G
  rw [energyForm_eq_neg_generator, energyForm_eq_neg_generator] at h
  simp only [mul_neg, expectation_neg] at h
  linarith

/-- The finite generator is negative semidefinite when the stirring rate is nonnegative. -/
theorem expectation_mul_generator_nonpos (ρ : Density) (E : Finset (V × V))
    {δ : ℝ} (hδ : 0 ≤ δ) (F : Config V → ℝ) :
    expectation ρ (fun η => F η * generator E δ F η) ≤ 0 := by
  have h := energy_nonneg ρ E hδ F
  rw [energy, energyForm_eq_neg_generator] at h
  simp only [mul_neg, expectation_neg] at h
  linarith

/-- A correction is supported on the interior set if its value depends only on those labels. -/
def DependsOnlyOn (I : Finset V) (F : Config V → ℝ) : Prop :=
  ∀ η ζ, (∀ x ∈ I, η x = ζ x) → F η = F ζ

omit [Fintype V] [DecidableEq V] in
theorem dependsOnlyOn_const (I : Finset V) (c : ℝ) : DependsOnlyOn I (fun _ => c) := by
  intro _ _ _
  rfl

/-- Admissible energy values in the unnormalized finite Dirichlet cell problem. -/
def admissibleEnergies (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    (δ : ℝ) (ℓ : Config V → ℝ) : Set ℝ :=
  {q | ∃ φ : Config V → ℝ, DependsOnlyOn I φ ∧ q = energy ρ E δ (fun η => ℓ η + φ η)}

def primalEnergy (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    (δ : ℝ) (ℓ : Config V → ℝ) : ℝ :=
  sInf (admissibleEnergies ρ E I δ ℓ)

theorem admissibleEnergies_nonempty (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    (δ : ℝ) (ℓ : Config V → ℝ) : (admissibleEnergies ρ E I δ ℓ).Nonempty := by
  exact ⟨_, (fun _ => 0), dependsOnlyOn_const I 0, rfl⟩

theorem admissibleEnergies_bddBelow (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    BddBelow (admissibleEnergies ρ E I δ ℓ) := by
  refine ⟨0, ?_⟩
  rintro q ⟨φ, _, rfl⟩
  exact energy_nonneg ρ E hδ _

theorem primalEnergy_nonneg (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) : 0 ≤ primalEnergy ρ E I δ ℓ := by
  apply le_csInf (admissibleEnergies_nonempty ρ E I δ ℓ)
  rintro q ⟨φ, _, rfl⟩
  exact energy_nonneg ρ E hδ _

theorem primalEnergy_le_competitor (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ φ : Config V → ℝ) (hφ : DependsOnlyOn I φ) :
    primalEnergy ρ E I δ ℓ ≤ energy ρ E δ (fun η => ℓ η + φ η) := by
  exact csInf_le (admissibleEnergies_bddBelow ρ E I hδ ℓ) ⟨φ, hφ, rfl⟩

theorem primalEnergy_le_affine (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {δ : ℝ} (hδ : 0 ≤ δ) (ℓ : Config V → ℝ) :
    primalEnergy ρ E I δ ℓ ≤ energy ρ E δ ℓ := by
  simpa using primalEnergy_le_competitor ρ E I hδ ℓ (fun _ => 0) (dependsOnlyOn_const I 0)

theorem primalEnergy_mono (ρ : Density) (E : Finset (V × V)) (I : Finset V)
    {ε δ : ℝ} (hε : 0 ≤ ε) (h : ε ≤ δ) (ℓ : Config V → ℝ) :
    primalEnergy ρ E I ε ℓ ≤ primalEnergy ρ E I δ ℓ := by
  apply le_csInf (admissibleEnergies_nonempty ρ E I δ ℓ)
  rintro q ⟨φ, hφ, rfl⟩
  exact (primalEnergy_le_competitor ρ E I hε ℓ φ hφ).trans (energy_mono ρ E h _)

end TwoColor
