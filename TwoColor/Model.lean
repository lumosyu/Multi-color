import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The microscopic two-color exclusion model

Concrete configurations, exchanges, species indicators, and bond rates from Section 1.1
of *Algebraic approximation for two-color exclusion and a quenched invariance principle
for the tagged particle* (September 2026).

Vacancy, red, and blue are respectively the elements `0`, `1`, and `2` of `Fin 3`.
The definitions work on any site type with decidable equality, including finite cells and
the lattice `Site d`. No stochastic process or limit theorem is assumed in this file.
-/

namespace TwoColor

abbrev Site (d : ℕ) := Fin d → ℤ

abbrev Color := Fin 3

abbrev Config (V : Type*) := V → Color

variable {V : Type*} [DecidableEq V]

/-- Exchange the labels at the two endpoints of a bond. -/
def exchange (η : Config V) (x y : V) : Config V :=
  fun z => η (Equiv.swap x y z)

@[simp] theorem exchange_apply_left (η : Config V) (x y : V) :
    exchange η x y x = η y := by
  simp [exchange]

@[simp] theorem exchange_apply_right (η : Config V) (x y : V) :
    exchange η x y y = η x := by
  simp [exchange]

theorem exchange_apply_of_ne (η : Config V) (x y z : V)
    (hx : z ≠ x) (hy : z ≠ y) : exchange η x y z = η z := by
  simp [exchange, Equiv.swap_apply_of_ne_of_ne hx hy]

@[simp] theorem exchange_self (η : Config V) (x : V) :
    exchange η x x = η := by
  funext z
  simp [exchange]

theorem exchange_symm (η : Config V) (x y : V) :
    exchange η x y = exchange η y x := by
  unfold exchange
  rw [Equiv.swap_comm x y]

@[simp] theorem exchange_exchange (η : Config V) (x y : V) :
    exchange (exchange η x y) x y = η := by
  funext z
  simp [exchange]

/-- The real-valued indicator of a species at a site. -/
def indicator (i : Color) (η : Config V) (x : V) : ℝ :=
  if η x = i then 1 else 0

/-- Occupation is the sum of the red and blue indicators. -/
def occupation (η : Config V) (x : V) : ℝ :=
  indicator 1 η x + indicator 2 η x

omit [DecidableEq V] in
theorem occupation_eq (η : Config V) (x : V) :
    occupation η x = if η x = 0 then 0 else 1 := by
  unfold occupation indicator
  generalize η x = c
  fin_cases c <;> norm_num <;> decide

@[simp] theorem indicator_exchange_left (i : Color) (η : Config V) (x y : V) :
    indicator i (exchange η x y) x = indicator i η y := by
  simp [indicator]

@[simp] theorem indicator_exchange_right (i : Color) (η : Config V) (x y : V) :
    indicator i (exchange η x y) y = indicator i η x := by
  simp [indicator]

@[simp] theorem occupation_exchange_left (η : Config V) (x y : V) :
    occupation (exchange η x y) x = occupation η y := by
  simp [occupation]

@[simp] theorem occupation_exchange_right (η : Config V) (x y : V) :
    occupation (exchange η x y) y = occupation η x := by
  simp [occupation]

/-- Rate one for a bond touching a vacancy, and rate `δ` for two occupied endpoints. -/
def rate (δ : ℝ) (η : Config V) (x y : V) : ℝ :=
  if η x = 0 ∨ η y = 0 then 1 else δ

omit [DecidableEq V] in
/-- Agreement with the occupation-variable formula displayed in the paper. -/
theorem rate_eq_occupation (δ : ℝ) (η : Config V) (x y : V) :
    rate δ η x y =
      (if occupation η x * occupation η y = 0 then 1 else 0) +
        δ * occupation η x * occupation η y := by
  simp only [rate, occupation_eq]
  by_cases hx : η x = 0 <;> by_cases hy : η y = 0 <;> simp [hx, hy]

omit [DecidableEq V] in
theorem rate_symm (δ : ℝ) (η : Config V) (x y : V) :
    rate δ η x y = rate δ η y x := by
  simp only [rate, or_comm]

@[simp] theorem rate_exchange (δ : ℝ) (η : Config V) (x y : V) :
    rate δ (exchange η x y) x y = rate δ η x y := by
  simp only [rate, exchange_apply_left, exchange_apply_right, or_comm]

omit [DecidableEq V] in
@[simp] theorem rate_one (η : Config V) (x y : V) :
    rate 1 η x y = 1 := by
  simp [rate]

omit [DecidableEq V] in
theorem rate_of_vacancy (δ : ℝ) (η : Config V) (x y : V)
    (h : η x = 0 ∨ η y = 0) : rate δ η x y = 1 := by
  simp [rate, h]

omit [DecidableEq V] in
theorem rate_of_occupied (δ : ℝ) (η : Config V) (x y : V)
    (hx : η x ≠ 0) (hy : η y ≠ 0) : rate δ η x y = δ := by
  simp [rate, hx, hy]

omit [DecidableEq V] in
theorem le_rate (δ : ℝ) (η : Config V) (x y : V) (hδ : δ ≤ 1) :
    δ ≤ rate δ η x y := by
  unfold rate
  split
  · exact hδ
  · exact le_rfl

omit [DecidableEq V] in
theorem rate_le_one (δ : ℝ) (η : Config V) (x y : V) (hδ : δ ≤ 1) :
    rate δ η x y ≤ 1 := by
  unfold rate
  split
  · exact le_rfl
  · exact hδ

omit [DecidableEq V] in
theorem rate_nonneg (δ : ℝ) (η : Config V) (x y : V) (hδ : 0 ≤ δ) :
    0 ≤ rate δ η x y := by
  unfold rate
  split
  · exact zero_le_one
  · exact hδ

omit [DecidableEq V] in
theorem rate_mono (ε δ : ℝ) (η : Config V) (x y : V) (h : ε ≤ δ) :
    rate ε η x y ≤ rate δ η x y := by
  unfold rate
  split
  · exact le_rfl
  · exact h

/-- The exchange gradient `π_{x,y} F`. -/
def exchangeDiff (F : Config V → ℝ) (x y : V) (η : Config V) : ℝ :=
  F (exchange η x y) - F η

@[simp] theorem exchangeDiff_self (F : Config V → ℝ) (x : V) (η : Config V) :
    exchangeDiff F x x η = 0 := by
  simp [exchangeDiff]

theorem exchangeDiff_symm (F : Config V → ℝ) (x y : V) (η : Config V) :
    exchangeDiff F x y η = exchangeDiff F y x η := by
  rw [exchangeDiff, exchangeDiff, exchange_symm η x y]

@[simp] theorem exchangeDiff_exchange (F : Config V → ℝ) (x y : V) (η : Config V) :
    exchangeDiff F x y (exchange η x y) = -exchangeDiff F x y η := by
  simp [exchangeDiff, neg_sub]

@[simp] theorem exchangeDiff_const (c : ℝ) (x y : V) (η : Config V) :
    exchangeDiff (fun _ => c) x y η = 0 := by
  simp [exchangeDiff]

end TwoColor
