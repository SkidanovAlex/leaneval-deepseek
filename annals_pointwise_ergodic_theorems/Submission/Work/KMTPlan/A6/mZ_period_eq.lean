/-
# The arithmetic symbol `m_Ẑ` does not depend on the chosen common period

The arithmetic symbol of the §6 model approximation (`mod-approx` of Krause--Mirek--Tao,
*Pointwise ergodic theorems for non-conventional bilinear polynomial averages*, Ann. of Math.
195 (3) 2022) is

  `m_Ẑ(α₁,α₂) = E_{n ∈ ℤ/qℤ} e(α₁ n + α₂ P(n))`,

i.e. the average of the arithmetic character `arithW P α₁ α₂ n = e(α₁n + α₂P(n))` over `q`
consecutive integers — a legitimate average over `ℤ/qℤ` precisely when `q • α₁ = q • α₂ = 0`.

This file proves that the value is *independent of the choice of such a period*: if both `q` and
`q'` kill `α₁` and `α₂`, then `mZ P q α₁ α₂ = mZ P q' α₁ α₂`.  The reason is that the character is
`q`-periodic (`arithW_period`, `arithW_period_mul`), so averaging it over `q` consecutive integers
and over `q'` consecutive integers are both the average over `ℤ/lcm(q,q')`, and the average of a
`q`-periodic function over a multiple of `q` terms is the average over `q` terms.

The proof is the elementary averaging lemma `sum_range_mul_of_periodic`: for a `q`-periodic
`u : ℕ → ℂ` one has `∑_{i<qk} u i = k ∑_{i<q} u i`.
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_M0_defs

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6

open Polynomial Finset
open scoped BigOperators
open Work.KMTAreas.A7

noncomputable section

/-! ## Elementary averaging of a periodic sequence -/

/-- If `u : ℕ → ℂ` has `u (n + l) = u n` for all `n`, then `u (n + l * m) = u n`. -/
private lemma periodic_mul_right (u : ℕ → ℂ) {l : ℕ} (hper : ∀ n : ℕ, u (n + l) = u n) :
    ∀ n m : ℕ, u (n + l * m) = u n := by
  intro n m
  induction m with
  | zero => simp
  | succ k ih =>
      have h : n + l * (k + 1) = (n + l * k) + l := by rw [Nat.mul_succ, Nat.add_assoc]
      rw [h, hper, ih]

/-- **Averaging a periodic sequence over a multiple of its period.**
If `u (n + l) = u n` for all `n`, then every block of `l` consecutive values of `u` has the same
sum, hence `∑_{i < l k} u i = k ∑_{i < l} u i`. -/
private lemma sum_range_mul_of_periodic (u : ℕ → ℂ) {l : ℕ}
    (hper : ∀ n : ℕ, u (n + l) = u n) :
    ∀ k : ℕ, ∑ i ∈ Finset.range (l * k), u i = (k : ℂ) * ∑ i ∈ Finset.range l, u i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hsplit : ∑ i ∈ Finset.range (l * (k + 1)), u i
          = ∑ i ∈ Finset.range (l * k), u i + ∑ i ∈ Finset.range l, u (l * k + i) := by
        rw [Nat.mul_succ, Finset.sum_range_add]
      have hconst : ∑ i ∈ Finset.range l, u (l * k + i) = ∑ i ∈ Finset.range l, u i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have h := periodic_mul_right u hper i k
        rwa [Nat.add_comm (l * k) i]
      rw [hsplit, hconst, ih, Nat.cast_succ]
      ring

/-- **`mZ` is unchanged when the period is multiplied by a positive integer.**  If `l > 0`, `k > 0`
and the arithmetic character is `l`-periodic, then averaging over `l k` consecutive integers gives
the same value as averaging over `l` of them. -/
private lemma mZ_mul_eq (P : Polynomial ℤ) (γ₁ γ₂ : Work.Analysis.IonescuWainger.Circle)
    {l k : ℕ} (hl : 0 < l) (hk : 0 < k)
    (hper : ∀ n : ℕ, Work.A7.arithW P γ₁ γ₂ ((n + l : ℕ) : ℤ)
      = Work.A7.arithW P γ₁ γ₂ (n : ℤ)) :
    mZ P l γ₁ γ₂ = mZ P (l * k) γ₁ γ₂ := by
  have hmZ : ∀ N : ℕ, mZ P N γ₁ γ₂
      = ((N : ℂ))⁻¹ * ∑ a ∈ Finset.range N, Work.A7.arithW P γ₁ γ₂ (a : ℤ) := fun N => rfl
  have hsum := sum_range_mul_of_periodic (fun a : ℕ => Work.A7.arithW P γ₁ γ₂ (a : ℤ)) hper k
  rw [hmZ l, hmZ (l * k), hsum, Nat.cast_mul]
  have hlC : ((l : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hl
  have hkC : ((k : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hk
  field_simp

/-! ## The main statement -/

theorem mZ_period_eq (P : Polynomial ℤ) {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    {γ₁ γ₂ : AddCircle (1 : ℝ)} (h₁ : q • γ₁ = 0) (h₂ : q • γ₂ = 0)
    (h₁' : q' • γ₁ = 0) (h₂' : q' • γ₂ = 0) :
    Work.KMTAreas.A7.mZ P q γ₁ γ₂ = Work.KMTAreas.A7.mZ P q' γ₁ γ₂ := by
  -- the arithmetic character is `q`-periodic and `q'`-periodic
  have hper_q : ∀ n : ℕ, Work.A7.arithW P γ₁ γ₂ ((n + q : ℕ) : ℤ)
      = Work.A7.arithW P γ₁ γ₂ (n : ℤ) := by
    intro n
    have h := Work.A7.arithW_period P q γ₁ γ₂ h₁ h₂ (n : ℤ)
    have hcast : ((n + q : ℕ) : ℤ) = (n : ℤ) + (q : ℤ) := by push_cast; ring
    rw [hcast]
    exact h
  have hper_q' : ∀ n : ℕ, Work.A7.arithW P γ₁ γ₂ ((n + q' : ℕ) : ℤ)
      = Work.A7.arithW P γ₁ γ₂ (n : ℤ) := by
    intro n
    have h := Work.A7.arithW_period P q' γ₁ γ₂ h₁' h₂' (n : ℤ)
    have hcast : ((n + q' : ℕ) : ℤ) = (n : ℤ) + (q' : ℤ) := by push_cast; ring
    rw [hcast]
    exact h
  -- both averages equal the average over `q * q'` consecutive integers
  have hq_eq : mZ P q γ₁ γ₂ = mZ P (q * q') γ₁ γ₂ := mZ_mul_eq P γ₁ γ₂ hq hq' hper_q
  have hq'_eq : mZ P q' γ₁ γ₂ = mZ P (q' * q) γ₁ γ₂ := mZ_mul_eq P γ₁ γ₂ hq' hq hper_q'
  rw [hq_eq, hq'_eq, Nat.mul_comm q' q]

end

end Work.KMTPlan.A6
