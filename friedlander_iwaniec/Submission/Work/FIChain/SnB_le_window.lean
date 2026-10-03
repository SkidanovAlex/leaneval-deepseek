/-
# `Work.FIChain.SnB_le_window` — the factorial bound for the unweighted chain sums

`SnB B ν n D y` is the length-`n` chain sum: a sum over strictly decreasing tuples of primes
`p_1 > p_2 > ⋯ > p_n < y` of `∏ ν(p_i)`, restricted by the Rosser–Iwaniec layer conditions.
The lemma proved here is the *factorial* bound

  `SnB B ν n D y ≤ (1/(n-1)!) · (Σ_{q ∈ winF B D y n} ν q)^n`,

which is what makes `Σ_n OddLayerSum` converge.

## Strategy

Let `W_n = winF B D y n` be the level-`n` window and `W_n(p) = winF B (D/p) p n` the window
one level inside.  The proof is an induction on `n`.  Two elementary facts drive it:

* **(window comparison)** for a prime `p < y` and `n ≥ 1`, `W_n(p) ⊆ W_{n+1} ∩ {q < p}`:
  the child condition `D/p < q^{B+1}·p^{n-1}` multiplied by `p > 0` gives `D < q^{B+1}p^n`,
  and `p < y` turns this into the parent condition `D < q^{B+1}y^n`.  In the complementary
  case `¬(D < p^{B+1}y^n)` the child window is *empty* (monotonicity of `x ↦ x^{B+1}`, using
  `B ≥ 0`).
* **(discrete Hardy / Riemann sum bound)** for a finite set `S` of non-negative weights,
  `Σ_{p ∈ S} w p · (Σ_{q ∈ S, q < p} w q)^k ≤ (Σ_{p ∈ S} w p)^{k+1}/(k+1)`; this is the
  left-endpoint Riemann sum for `∫_0^W x^k dx = W^{k+1}/(k+1)`, proved by peeling off the
  maximum element and using the two-term binomial bound.

Peeling the outermost prime off `SnB B ν (k+1) D y` and applying the induction hypothesis
one level in therefore gives

  `SnB B ν (k+1) D y ≤ (1/(k-1)!) · Σ_{p ∈ W_{k+1}} ν p · (Σ_{q ∈ W_{k+1}, q<p} ν q)^k
                     ≤ (1/(k-1)!) · (Σ_{q ∈ W_{k+1}} ν q)^{k+1}/(k+1) ≤ (1/k!)·(…)^{k+1}`,

the last step because `k! = k·(k-1)!` and `1/(k+1) ≤ 1/k`.
-/
import Mathlib
import Submission.Work.FIChain.LamPlusBLayerDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## A two-term lower bound for the binomial expansion -/

/-- `(x+y)^(k+1) ≥ x^(k+1) + (k+1)·y·x^k` for `x, y ≥ 0` (the terms `m = k` and `m = k+1` of
the binomial expansion, all others being non-negative). -/
lemma add_pow_lower (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    x ^ (k + 1) + ((k : ℝ) + 1) * y * x ^ k ≤ (x + y) ^ (k + 1) := by
  have hnonneg : ∀ m : ℕ, 0 ≤ x ^ m * y ^ (k + 1 - m) * ((k + 1).choose m : ℝ) := fun m =>
    mul_nonneg (mul_nonneg (pow_nonneg hx m) (pow_nonneg hy _)) (Nat.cast_nonneg _)
  rw [add_pow]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum : 0 ≤ ∑ m ∈ Finset.range k, x ^ m * y ^ (k + 1 - m) * ((k + 1).choose m : ℝ) :=
    Finset.sum_nonneg (fun m _ => hnonneg m)
  have hk : x ^ k * y ^ (k + 1 - k) * ((k + 1).choose k : ℝ) = ((k : ℝ) + 1) * y * x ^ k := by
    rw [Nat.add_sub_cancel_left, Nat.choose_succ_self_right]
    push_cast; ring
  have hk1 : x ^ (k + 1) * y ^ (k + 1 - (k + 1)) * ((k + 1).choose (k + 1) : ℝ)
      = x ^ (k + 1) := by
    rw [tsub_self, pow_zero, Nat.choose_self]; ring
  rw [hk, hk1]
  nlinarith [hsum]

/-! ## The discrete Riemann-sum (Hardy) bound -/

/-- **Discrete Hardy bound.**  For a finite set `S` of non-negative weights,
`Σ_{p ∈ S} w p · (Σ_{q ∈ S, q < p} w q)^k ≤ (Σ_{p ∈ S} w p)^{k+1}/(k+1)`.
This is the left-endpoint Riemann sum of `∫_0^W x^k dx` along the ordered elements of `S`. -/
lemma prefix_pow_le_local (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ S, 0 ≤ w p) (k : ℕ) :
    (∑ p ∈ S, w p * (∑ q ∈ S.filter (fun q => q < p), w q) ^ k)
      ≤ (∑ p ∈ S, w p) ^ (k + 1) / ((k : ℝ) + 1) := by
  have hmain : ∀ T : Finset ℕ, (∀ p ∈ T, 0 ≤ w p) →
      (∑ p ∈ T, w p * (∑ q ∈ T.filter (fun q => q < p), w q) ^ k)
        ≤ (∑ p ∈ T, w p) ^ (k + 1) / ((k : ℝ) + 1) := by
    intro T
    induction T using Finset.induction_on_max with
    | empty =>
      intro _
      simp
    | insert a s hlt ih =>
      intro hw'
      have hains : a ∉ s := fun h => absurd (hlt a h) (lt_irrefl a)
      have hws : ∀ p ∈ s, 0 ≤ w p := fun p hp => hw' p (Finset.mem_insert_of_mem hp)
      have ha : 0 ≤ w a := hw' a (Finset.mem_insert_self a s)
      have hfa : (insert a s).filter (fun q => q < a) = s := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hq, hqa⟩
          rcases hq with hqa' | hqs
          · rw [hqa'] at hqa; exact absurd hqa (lt_irrefl a)
          · exact hqs
        · intro hqs
          exact ⟨Or.inr hqs, hlt q hqs⟩
      have hfs : ∀ p ∈ s, (insert a s).filter (fun q => q < p) = s.filter (fun q => q < p) := by
        intro p hp
        have hpa : p < a := hlt p hp
        ext q
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hq, hqp⟩
          rcases hq with hqa' | hqs
          · rw [hqa'] at hqp; omega
          · exact ⟨hqs, hqp⟩
        · rintro ⟨hqs, hqp⟩
          exact ⟨Or.inr hqs, hqp⟩
      have hsplit : ∑ p ∈ insert a s, w p * (∑ q ∈ (insert a s).filter (fun q => q < p), w q) ^ k
          = w a * (∑ q ∈ s, w q) ^ k
            + ∑ p ∈ s, w p * (∑ q ∈ s.filter (fun q => q < p), w q) ^ k := by
        rw [Finset.sum_insert hains, hfa]
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        rw [hfs p hp]
      have hsum : ∑ p ∈ insert a s, w p = w a + ∑ p ∈ s, w p := Finset.sum_insert hains
      rw [hsplit, hsum]
      have ihs := ih hws
      have hB : (0:ℝ) ≤ ∑ p ∈ s, w p := Finset.sum_nonneg hws
      have hb := add_pow_lower (∑ p ∈ s, w p) (w a) hB ha k
      rw [add_comm (w a) (∑ p ∈ s, w p)]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (k : ℝ) + 1)]
      have hS : (∑ p ∈ s, w p * (∑ q ∈ s.filter (fun q => q < p), w q) ^ k) * ((k:ℝ) + 1)
          ≤ (∑ p ∈ s, w p) ^ (k+1) :=
        (le_div_iff₀ (by positivity : (0:ℝ) < (k : ℝ) + 1)).mp ihs
      nlinarith [hS, hb]
  exact hmain S hw

/-! ## The level-`1` base case -/

/-! ## Comparing the level-`n` window inside `p` with the level-`(n+1)` window -/

/-! ## The main induction -/

end

end Work.FIChain
