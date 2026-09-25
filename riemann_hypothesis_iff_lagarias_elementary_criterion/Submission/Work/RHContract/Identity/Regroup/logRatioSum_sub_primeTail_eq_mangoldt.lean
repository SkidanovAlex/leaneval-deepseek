import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# `Work.RHContract.Identity.Regroup.logRatioSum_sub_primeTail_eq_mangoldt`

The elementary regrouping identity (step 1 of the Mertens identity, Lemma I):

`logRatioSum x − primeTail x = ∑_{n ≤ ⌊x⌋} Λ n / (n log n)`   for `x ≥ 2`.

Both sides are the same double sum over prime powers `p^k`:

* `logRatioSum x = ∑_{p ≤ ⌊x⌋} log (p/(p−1)) = ∑_{p ≤ ⌊x⌋} ∑_{k ≥ 1} 1/(k p^k)`;
* `primeTail x` removes from the `p`-th series the terms with `k > e_p`, `e_p = Nat.log p ⌊x⌋`
  being the exponent of `p` in `lcm(1..⌊x⌋)`, i.e. `p^{e_p} ≤ ⌊x⌋ < p^{e_p+1}`;
* so the difference is `∑_{p ≤ ⌊x⌋} ∑_{k = 1}^{e_p} 1/(k p^k) = ∑_{p^k ≤ ⌊x⌋} 1/(k p^k)`;
* and `∑_{n ≤ ⌊x⌋} Λ n/(n log n) = ∑_{n = p^k ≤ ⌊x⌋} log p/(p^k · k log p)
   = ∑_{p^k ≤ ⌊x⌋} 1/(k p^k)`.
-/

namespace Work.RHContract.Identity.Regroup

open Finset
open scoped BigOperators

/-- `log (p/(p−1)) = −log (1 − 1/p)` for `p ≥ 2`. -/
private lemma log_div_pred_eq_neg_log (p : ℕ) (hp : 2 ≤ p) :
    Real.log ((p : ℝ) / ((p : ℝ) - 1)) = -Real.log (1 - 1 / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    exact ne_of_gt this
  have h1 : (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
    field_simp
  have h2 : (p : ℝ) / ((p : ℝ) - 1) = (1 - 1 / (p : ℝ))⁻¹ := by
    rw [h1, inv_div]
  rw [h2, Real.log_inv]

/-- For a prime `p`, the exponent range `1 ≤ k ≤ Nat.log p N` is the set of `k ≤ N`
with `p^k ≤ N`. -/
private lemma Icc_log_eq_filter (p N : ℕ) (hp : Nat.Prime p) :
    Finset.Icc 1 (Nat.log p N) = (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N) := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [Nat.log_zero_right, Finset.Icc_eq_empty_iff.mpr (by omega), Finset.filter_empty]
  ext k
  rw [Finset.mem_Icc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, le_trans h2 (Nat.log_le_self p N)⟩, Nat.pow_le_of_le_log hN h2⟩
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, Nat.le_log_of_pow_le hp.one_lt h3⟩

/-- Regrouping the double sum over prime powers as a single sum over the prime powers
`n ≤ N`. -/
private lemma sum_prime_pow_eq_vonMangoldt (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, ∑ k ∈ Finset.Icc 1 (Nat.log p N), 1 / ((k : ℝ) * (p : ℝ) ^ k))
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n),
          Real.log (Nat.minFac n) / ((n : ℝ) * Real.log (n : ℝ)) := by
  classical
  have hE1 : (∑ p ∈ Nat.primesLE N, ∑ k ∈ Finset.Icc 1 (Nat.log p N),
        1 / ((k : ℝ) * (p : ℝ) ^ k))
      = ∑ p ∈ Nat.primesLE N, ∑ k ∈ Finset.Icc 1 N,
          (if p ^ k ≤ N then 1 / ((k : ℝ) * (p : ℝ) ^ k) else 0) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Icc_log_eq_filter p N (Nat.prime_of_mem_primesLE hp)]
    exact Finset.sum_filter _ _
  have hE2 : (∑ p ∈ Nat.primesLE N, ∑ k ∈ Finset.Icc 1 N,
          (if p ^ k ≤ N then 1 / ((k : ℝ) * (p : ℝ) ^ k) else 0))
      = ∑ pk ∈ (Nat.primesLE N ×ˢ Finset.Icc 1 N).filter
            (fun pk : ℕ × ℕ => pk.1 ^ pk.2 ≤ N),
          1 / ((pk.2 : ℝ) * (pk.1 : ℝ) ^ pk.2) := by
    rw [Finset.sum_filter, Finset.sum_product]
  have hbij : (∑ pk ∈ (Nat.primesLE N ×ˢ Finset.Icc 1 N).filter
            (fun pk : ℕ × ℕ => pk.1 ^ pk.2 ≤ N),
          1 / ((pk.2 : ℝ) * (pk.1 : ℝ) ^ pk.2))
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n),
          Real.log (Nat.minFac n) / ((n : ℝ) * Real.log (n : ℝ)) := by
    refine Finset.sum_bij (fun pk (_ : pk ∈ _) => pk.1 ^ pk.2) ?_ ?_ ?_ ?_
    · -- the image is a subset of the prime powers below `N`
      intro pk hpk
      rw [Finset.mem_filter] at hpk
      obtain ⟨hpkU, hle⟩ := hpk
      rw [Finset.mem_product, Nat.mem_primesLE] at hpkU
      obtain ⟨⟨_, hpprime⟩, hkIcc⟩ := hpkU
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨one_le_pow₀ hpprime.one_le, hle⟩, ?_⟩
      exact (hpprime.isPrimePow).pow (by have := (Finset.mem_Icc.mp hkIcc).1; omega)
    · -- injectivity
      intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      obtain ⟨haU, _⟩ := ha
      obtain ⟨hbU, _⟩ := hb
      rw [Finset.mem_product, Nat.mem_primesLE] at haU hbU
      obtain ⟨⟨_, hpaprime⟩, hka⟩ := haU
      obtain ⟨⟨_, hpbprime⟩, hkb⟩ := hbU
      have hka0 : a.2 ≠ 0 := by have := (Finset.mem_Icc.mp hka).1; omega
      have hkb0 : b.2 ≠ 0 := by have := (Finset.mem_Icc.mp hkb).1; omega
      obtain ⟨h1, h2⟩ := hpaprime.pow_inj' hpbprime hka0 hkb0 hab
      exact Prod.ext h1 h2
    · -- surjectivity
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨_, hnN⟩, hispp⟩ := hn
      rw [isPrimePow_nat_iff] at hispp
      obtain ⟨p, k, hp, hkpos, hpk⟩ := hispp
      have hpN : p ≤ N := by
        calc p ≤ p ^ k := le_self_pow₀ hp.one_le hkpos.ne'
          _ = n := hpk
          _ ≤ N := hnN
      have hkN : k ≤ N := by
        calc k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
          _ = n := hpk
          _ ≤ N := hnN
      refine ⟨(p, k), ?_, hpk⟩
      rw [Finset.mem_filter, Finset.mem_product, Nat.mem_primesLE, Finset.mem_Icc]
      exact ⟨⟨⟨hpN, hp⟩, ⟨hkpos, hkN⟩⟩, by rw [hpk]; exact hnN⟩
    · -- the summands agree
      intro pk hpk
      rw [Finset.mem_filter] at hpk
      obtain ⟨hpkU, _⟩ := hpk
      rw [Finset.mem_product, Nat.mem_primesLE] at hpkU
      obtain ⟨⟨_, hpprime⟩, hkIcc⟩ := hpkU
      have hk0 : pk.2 ≠ 0 := by have := (Finset.mem_Icc.mp hkIcc).1; omega
      have hmin : (pk.1 ^ pk.2).minFac = pk.1 := hpprime.pow_minFac hk0
      have hlog : Real.log (((pk.1 ^ pk.2 : ℕ)) : ℝ)
          = (pk.2 : ℝ) * Real.log (pk.1 : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
      have hlogp : Real.log (pk.1 : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast hpprime.one_lt))
      have hk0R : (pk.2 : ℝ) ≠ 0 := by exact_mod_cast hk0
      have hp0R : (pk.1 : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (pk.1 : ℝ) := by exact_mod_cast hpprime.pos
        exact ne_of_gt this
      show 1 / ((pk.2 : ℝ) * (pk.1 : ℝ) ^ pk.2)
          = Real.log (Nat.minFac (pk.1 ^ pk.2))
              / (((pk.1 ^ pk.2 : ℕ) : ℝ) * Real.log (((pk.1 ^ pk.2 : ℕ)) : ℝ))
      rw [hmin, hlog, Nat.cast_pow]
      field_simp
  exact hE1.trans (hE2.trans hbij)

theorem logRatioSum_sub_primeTail_eq_mangoldt (x : ℝ) (hx : 2 ≤ x) :
    Commons.NumberTheory.Mertens.logRatioSum x - Work.RHContract.primeTail x
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (ArithmeticFunction.vonMangoldt n : ℝ) / ((n : ℝ) * Real.log (n : ℝ)) := by
  have hL : Commons.NumberTheory.Mertens.logRatioSum x - Work.RHContract.primeTail x
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊, ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊),
          1 / ((k : ℝ) * (p : ℝ) ^ k) := by
    simp only [Commons.NumberTheory.Mertens.logRatioSum, Work.RHContract.primeTail]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE hp
    have hlog := log_div_pred_eq_neg_log p hp2
    rw [hlog]
    ring
  rw [hL, sum_prime_pow_eq_vonMangoldt ⌊x⌋₊]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [ArithmeticFunction.vonMangoldt_apply]
  by_cases h : IsPrimePow n <;> simp [h]

end Work.RHContract.Identity.Regroup
