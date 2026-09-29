import Mathlib
import Submission.CDT.RatFuncOrder

/-!
# The `WithTop ℤ`-valued order of vanishing

`ordAtT α x` is `ordAt α x` with the value `⊤` at `x = 0`.  This is the
correct "valuation" for a *sum*: the `min`-rule and the strict-dominance rule
hold with no side conditions, which is exactly what the Frobenius/indicial
analysis of a linear differential operator needs when some of the terms of the
operator are allowed to vanish identically.

Main results: `ordAtT_add_ge` (the `min` rule), `ordAtT_mul` (additivity),
`ordAtT_algebraMap` (agreement with the root multiplicity), the strict
dominance rule `ordAtT_add_eq_of_le_succ`, its `Finset` versions
`le_ordAtT_finset_sum` / `ordAtT_finset_sum_eq`.
-/

open Classical

noncomputable section

namespace Submission.CDT

open Polynomial

set_option linter.unusedSimpArgs false

variable {K : Type*} [Field K]

/-- The order of vanishing with `⊤` at `0`.  It is a valuation: additive, with
`⊤` absorbing. -/
def ordAtT (α : K) (x : RatFunc K) : WithTop ℤ := if x = 0 then ⊤ else ↑(ordAt α x)

lemma ordAtT_eq_top_iff {α : K} {x : RatFunc K} : ordAtT α x = ⊤ ↔ x = 0 := by
  unfold ordAtT
  by_cases h : x = 0
  · simp [h]
  · simp [h, WithTop.coe_ne_top]

@[simp] lemma ordAtT_zero (α : K) : ordAtT α 0 = ⊤ := by simp [ordAtT]

lemma ordAtT_of_ne {α : K} {x : RatFunc K} (hx : x ≠ 0) :
    ordAtT α x = (ordAt α x : WithTop ℤ) := by simp [ordAtT, hx]

lemma ordAtT_ne_top_iff {α : K} {x : RatFunc K} : ordAtT α x ≠ ⊤ ↔ x ≠ 0 := by
  constructor
  · intro h hx; exact h (by rw [hx]; simp)
  · intro hx h; rw [ordAtT_eq_top_iff] at h; exact hx h

lemma ordAtT_eq_top_of_ne_top {α : K} {x : RatFunc K} (h : ordAtT α x ≠ ⊤) : x ≠ 0 :=
  (ordAtT_ne_top_iff).mp h

/-- `ordAtT` is invariant under negation. -/
lemma ordAtT_neg (α : K) (x : RatFunc K) : ordAtT α (-x) = ordAtT α x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [ordAtT_of_ne (neg_ne_zero.mpr hx), ordAtT_of_ne hx, ordAt_neg]

/-- The `min` rule for `ordAtT`, with no side condition. -/
lemma ordAtT_add_ge (α : K) (x y : RatFunc K) :
    min (ordAtT α x) (ordAtT α y) ≤ ordAtT α (x + y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · rw [hxy]; simp
  · rw [ordAtT_of_ne hx, ordAtT_of_ne hy, ordAtT_of_ne hxy, ← WithTop.coe_min]
    exact_mod_cast min_ordAt_le_ordAt_add α hxy

/-- Additivity of `ordAtT`. -/
lemma ordAtT_mul (α : K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAtT α (x * y) = ordAtT α x + ordAtT α y := by
  rw [ordAtT_of_ne (mul_ne_zero hx hy), ordAtT_of_ne hx, ordAtT_of_ne hy,
    ordAt_mul α hx hy, WithTop.coe_add]

@[simp] lemma ordAtT_one (α : K) : ordAtT α (1 : RatFunc K) = 0 := by
  rw [ordAtT_of_ne (one_ne_zero : (1 : RatFunc K) ≠ 0), ordAt_one]
  rfl

lemma ordAtT_inv (α : K) {x : RatFunc K} (hx : x ≠ 0) :
    ordAtT α x⁻¹ = -ordAtT α x := by
  rw [ordAtT_of_ne (inv_ne_zero hx), ordAtT_of_ne hx, ordAt_inv α hx]
  exact_mod_cast rfl

lemma ordAtT_div (α : K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAtT α (x / y) = ordAtT α x - ordAtT α y := by
  rw [div_eq_mul_inv, ordAtT_mul α hx (inv_ne_zero hy), ordAtT_inv α hy, sub_eq_add_neg]

/-- `ordAtT` of a nonnegative power. -/
lemma ordAtT_pow (α : K) {x : RatFunc K} (hx : x ≠ 0) (n : ℕ) :
    ordAtT α (x ^ n) = (n : ℤ) * ordAtT α x := by
  rw [ordAtT_of_ne (pow_ne_zero n hx), ordAtT_of_ne hx, ordAt_pow]
  push_cast
  rfl

/-- On nonzero polynomials, `ordAtT` is the root multiplicity (as an element of
`WithTop ℤ`). -/
lemma ordAtT_algebraMap {α : K} {p : Polynomial K} (hp : p ≠ 0) :
    ordAtT α (algebraMap (Polynomial K) (RatFunc K) p)
      = ((Polynomial.rootMultiplicity α p : ℤ) : WithTop ℤ) := by
  rw [ordAtT_of_ne (by simpa using hp), ordAt_algebraMap]

lemma ordAtT_algebraMap_eq_top {α : K} {p : Polynomial K} (hp : p = 0) :
    ordAtT α (algebraMap (Polynomial K) (RatFunc K) p) = ⊤ := by
  subst hp; simp

section StrictDominance

/-- **Strict dominance**: if `x` has order exactly `N` and `y` has order at
least `N+1`, the sum has order `N`. -/
lemma ordAtT_add_eq_of_le_succ {α : K} {x y : RatFunc K} {N : ℤ}
    (hx : ordAtT α x = (N : WithTop ℤ)) (hy : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α y) :
    ordAtT α (x + y) = (N : WithTop ℤ) := by
  have hxne : x ≠ 0 := by
    intro h
    rw [h, ordAtT_zero] at hx
    exact WithTop.coe_ne_top hx.symm
  rcases eq_or_ne y 0 with rfl | hyne
  · rw [add_zero]; exact hx
  have hx' : ordAt α x = N := by
    rw [ordAtT_of_ne hxne, WithTop.coe_eq_coe] at hx; exact hx
  have hy' : N + 1 ≤ ordAt α y := by
    rw [ordAtT_of_ne hyne, WithTop.coe_le_coe] at hy; exact hy
  have hlt : ordAt α x < ordAt α y := by rw [hx']; omega
  have hxy : x + y ≠ 0 := by
    intro h0
    have hyx : y = -x := eq_neg_of_add_eq_zero_right h0
    rw [hyx, ordAt_neg, hx'] at hy'
    omega
  rw [ordAtT_of_ne hxy, ordAt_add_of_lt α hxne hyne hlt, hx']

end StrictDominance

/-- If every term of a finite sum has order at least `N`, so does the sum. -/
lemma le_ordAtT_finset_sum {α : K} {ι : Type*} {s : Finset ι} {f : ι → RatFunc K} {N : ℤ}
    (h : ∀ i ∈ s, (N : WithTop ℤ) ≤ ordAtT α (f i)) :
    (N : WithTop ℤ) ≤ ordAtT α (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 : (N : WithTop ℤ) ≤ ordAtT α (f a) := h a (Finset.mem_insert_self a s)
      have h2 : (N : WithTop ℤ) ≤ ordAtT α (∑ i ∈ s, f i) :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      exact le_trans (le_min h1 h2) (ordAtT_add_ge α (f a) (∑ i ∈ s, f i))

/-- The `Finset` strict-dominance rule: if exactly one term of a finite sum has
order `N` and all the others have order at least `N+1`, the sum has order
`N`. -/
lemma ordAtT_finset_sum_eq {α : K} {ι : Type*} {s : Finset ι} {f : ι → RatFunc K}
    {i₀ : ι} {N : ℤ} (hi₀ : i₀ ∈ s) (hN : ordAtT α (f i₀) = (N : WithTop ℤ))
    (h : ∀ i ∈ s, i ≠ i₀ → ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (f i)) :
    ordAtT α (∑ i ∈ s, f i) = (N : WithTop ℤ) := by
  classical
  rw [← Finset.insert_erase hi₀, Finset.sum_insert (Finset.notMem_erase i₀ s)]
  refine ordAtT_add_eq_of_le_succ hN ?_
  exact le_ordAtT_finset_sum
    (fun i hi => h i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1)

end Submission.CDT
