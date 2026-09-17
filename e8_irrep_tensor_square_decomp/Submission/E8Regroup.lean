import Mathlib

/-!
# Regrouping a sum over the c-table terms

The dominant-chamber Freudenthal recursion for `L(ν)` at a dominant weight `μ` has one term per
positive root `α` and per `k ≥ 1`, and the value of the term is a weight multiplicity at
`η = μ + kα`; by `W`-invariance that multiplicity only depends on the dominant conjugate of `η`.

This file contains the *combinatorial* step: given a function `s : Fin 120 → Fin 4 → ℕ` (the index
of the dominant conjugate) and, for each `e : Fin 40`, the literal list `L e` of the terms whose
`s`-value is `e`, the ungrouped sum over the terms equals the sum over the `40` dominant weights
of the corresponding coefficient times `X` evaluated there.
-/

set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8Regroup

/-- `∑_{k ∈ Icc 1 4} f k = ∑_{k : Fin 4} f (k + 1)`. -/
theorem sum_Icc_one_four {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ k ∈ Finset.Icc 1 4, f k) = ∑ k : Fin 4, f (k.1 + 1) := by
  have h : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  rw [h, Fin.sum_univ_four]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-- The pointwise decomposition of `X ⟨s, _⟩` as a sum over `Fin 40`. -/
theorem ite_lt_eq_sum {s : ℕ} (hs : s < 40) (X : Fin 40 → ℤ) :
    X ⟨s, hs⟩ = ∑ e : Fin 40, (if s = e.1 then X e else 0) := by
  rw [Finset.sum_eq_single ⟨s, hs⟩]
  · rw [if_pos rfl]
  · intro e _ he
    rw [if_neg]
    intro hcon
    exact he (Fin.ext hcon.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ite_not_lt_eq_sum {s : ℕ} (hs : ¬ s < 40) (X : Fin 40 → ℤ) :
    (0 : ℤ) = ∑ e : Fin 40, (if s = e.1 then X e else 0) := by
  symm
  apply Finset.sum_eq_zero
  intro e _
  rw [if_neg]
  intro hcon
  exact hs (hcon ▸ e.2)

/-- **The regrouping lemma.** -/
theorem sum_regroup (b : Fin 120 → Fin 4 → ℤ) (s : Fin 120 → Fin 4 → ℕ)
    (L : Fin 40 → List (Fin 120 × Fin 4)) (X : Fin 40 → ℤ)
    (hmem : ∀ (j : Fin 120) (k : Fin 4) (h : s j k < 40), (j, k) ∈ L ⟨s j k, h⟩)
    (hsid : ∀ (e : Fin 40) (p : Fin 120 × Fin 4), p ∈ L e → s p.1 p.2 = e.1)
    (hnd : ∀ e : Fin 40, (L e).Nodup) :
    (∑ j : Fin 120, ∑ k : Fin 4,
        b j k * (if h : s j k < 40 then X ⟨s j k, h⟩ else 0))
      = ∑ e : Fin 40, ((L e).toFinset.sum fun p => b p.1 p.2) * X e := by
  classical
  have hstep : ∀ (j : Fin 120) (k : Fin 4),
      b j k * (if h : s j k < 40 then X ⟨s j k, h⟩ else 0)
        = ∑ e : Fin 40, b j k * (if s j k = e.1 then X e else 0) := by
    intro j k
    by_cases h : s j k < 40
    · rw [dif_pos h, ite_lt_eq_sum h X, Finset.mul_sum]
    · have h0 : (∑ i : Fin 40, (if s j k = i.1 then X i else 0)) = 0 :=
        (ite_not_lt_eq_sum h X).symm
      rw [dif_neg h, mul_zero]
      symm
      rw [← Finset.mul_sum, h0, mul_zero]
  have hfilter : ∀ e : Fin 40,
      (Finset.univ.filter fun p : Fin 120 × Fin 4 => s p.1 p.2 = e.1)
        = (L e).toFinset := by
    intro e
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    constructor
    · intro hp
      have hlt : s p.1 p.2 < 40 := by rw [hp]; exact e.2
      have := hmem p.1 p.2 hlt
      rwa [show (⟨s p.1 p.2, hlt⟩ : Fin 40) = e from Fin.ext hp] at this
    · intro hp
      exact hsid e p hp
  have hinner : ∀ e : Fin 40,
      (∑ j : Fin 120, ∑ k : Fin 4, b j k * (if s j k = e.1 then X e else 0))
        = ((L e).toFinset.sum fun p => b p.1 p.2) * X e := by
    intro e
    rw [← Fintype.sum_prod_type (f := fun p : Fin 120 × Fin 4 =>
      b p.1 p.2 * (if s p.1 p.2 = e.1 then X e else 0))]
    have h1 : ∀ p : Fin 120 × Fin 4,
        b p.1 p.2 * (if s p.1 p.2 = e.1 then X e else 0)
          = if s p.1 p.2 = e.1 then b p.1 p.2 * X e else 0 := by
      intro p
      by_cases hp : s p.1 p.2 = e.1
      · rw [if_pos hp, if_pos hp]
      · rw [if_neg hp, if_neg hp, mul_zero]
    simp only [h1]
    rw [← Finset.sum_filter, hfilter, Finset.sum_mul]
  simp only [hstep]
  have h2 : (∑ j : Fin 120, ∑ k : Fin 4, ∑ e : Fin 40,
        b j k * (if s j k = e.1 then X e else 0))
      = ∑ e : Fin 40, ∑ j : Fin 120, ∑ k : Fin 4,
        b j k * (if s j k = e.1 then X e else 0) := by
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
  rw [h2]
  exact Finset.sum_congr rfl (fun e _ => hinner e)

end Submission.E8Regroup
