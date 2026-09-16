import Submission.ZagierHoffmanProof.PrimeGreedy

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The greedy index and the closed form of the greedy fill

This module defines the "greedy index" `gidx p hp r n` (the least index `m` with
`r ≤ csum p n (m+1)`) directly by the same recursion as `Gg`, and proves the closed form

  `Gg p hp r n = ∑_{i < gidx} capp p n i * p^i + (r - csum p n gidx) * p ^ gidx`
-/

namespace ZagierHoffmanPositiveChar

/-- The sum of the first `m + 1` capacities is the capacity of digit `0` plus the sum over the
shifted capacities. -/
lemma csum_succ (p n m : ℕ) : csum p n (m + 1) = capp p n 0 + csum p (n / p) m := by
  unfold csum
  rw [Finset.sum_range_succ']
  have h : ∑ i ∈ Finset.range m, capp p n (i + 1) = ∑ i ∈ Finset.range m, capp p (n / p) i :=
    Finset.sum_congr rfl fun i _ => (capp_tail p n i).symm
  rw [h, add_comm]

lemma csum_succ_eq (p n m : ℕ) : csum p n (m + 1) - capp p n 0 = csum p (n / p) m := by
  rw [csum_succ, add_comm, Nat.add_sub_cancel]

/-- **The greedy index.**  The least index `m` at which the cumulative capacity reaches `r`. -/
def gidx (p : ℕ) (hp : 2 ≤ p) (r n : ℕ) : ℕ :=
  if r = 0 then 0
  else if capp p n 0 = 0 then gidx p hp r (n / p) + 1
  else if r ≤ capp p n 0 then 0
  else gidx p hp (r - capp p n 0) (n / p) + 1
termination_by r + n
decreasing_by
  all_goals simp_wf
  · have h0 : n % p = p - 1 := (capp_eq_zero_iff (by omega : 2 ≤ p)).mp ‹capp p n 0 = 0›
    have h1 : 1 ≤ n := by
      have hle : n % p ≤ n := Nat.mod_le n p
      omega
    have h2 : n / p < n := Nat.div_lt_self h1 (by omega)
    omega
  · have h2 : n / p ≤ n := Nat.div_le_self n p
    have h3 : 1 ≤ capp p n 0 := by
      rcases Nat.eq_zero_or_pos (capp p n 0) with h | h
      · exact absurd h ‹¬capp p n 0 = 0›
      · exact h
    omega

lemma gidx_eq_zero {p : ℕ} (hp : 2 ≤ p) {r n : ℕ} (hr : r ≤ p - 1) (h : r ≤ capp p n 0) :
    gidx p hp r n = 0 := by
  by_cases h1 : r = 0
  · rw [gidx, if_pos h1]
  · rw [gidx, if_neg h1]
    by_cases h2 : capp p n 0 = 0
    · rw [if_pos h2]
      omega
    · rw [if_neg h2, if_pos h]

lemma gidx_succ {p : ℕ} (hp : 2 ≤ p) {r n : ℕ} (hr : r ≤ p - 1) (h : capp p n 0 < r) :
    gidx p hp r n = gidx p hp (r - capp p n 0) (n / p) + 1 := by
  by_cases h1 : r = 0
  · omega
  · rw [gidx, if_neg h1]
    by_cases h2 : capp p n 0 = 0
    · rw [if_pos h2, h2, Nat.sub_zero]
    · rw [if_neg h2, if_neg (by omega : ¬ r ≤ capp p n 0)]

lemma gidx_le_self {p : ℕ} (hp : 2 ≤ p) (r n : ℕ) (hr : r ≤ p - 1) :
    gidx p hp r n ≤ n := by
  rw [gidx]
  split_ifs with h1 h2 h3
  · exact Nat.zero_le _
  · have h0 : n % p = p - 1 := (capp_eq_zero_iff hp).mp h2
    have hn1 : 1 ≤ n := by
      have hle : n % p ≤ n := Nat.mod_le n p
      omega
    have h4 : n / p < n := Nat.div_lt_self hn1 (by omega : 1 < p)
    have ih := gidx_le_self hp r (n / p) hr
    omega
  · exact Nat.zero_le _
  · have hc1 : 1 ≤ capp p n 0 := by omega
    have hcl : capp p n 0 ≤ p - 1 := capp_le p n 0
    have hn1 : 1 ≤ n := by
      have hle : n % p ≤ n := Nat.mod_le n p
      have h4 : capp p n 0 = p - 1 - n % p := capp_zero p n
      omega
    have ih := gidx_le_self hp (r - capp p n 0) (n / p) (by omega)
    have h5 : n / p < n := Nat.div_lt_self hn1 (by omega : 1 < p)
    omega

/-- The cumulative capacity at the greedy index does not yet reach `r`. -/
lemma csum_gidx_lt {p : ℕ} (hp : 2 ≤ p) : ∀ (r n : ℕ), r ≤ p - 1 → 0 < r →
    csum p n (gidx p hp r n) < r := by
  intro r n
  induction r, n using gidx.induct p hp with
  | case1 n => intro hr hr0; exact absurd hr0 (by omega)
  | case2 r n hr0 hc0 ih =>
      intro hr hpos
      rw [gidx_succ hp hr (by rw [hc0]; omega), csum_succ, hc0, Nat.zero_add]
      exact ih (by omega) hpos
  | case3 r n hr0 hc0 hle =>
      intro hr hpos
      rw [gidx_eq_zero hp hr hle]
      simp [csum]
      exact hpos
  | case4 r n hr0 hc0 hnc ih =>
      intro hr hpos
      have hclt : capp p n 0 < r := by omega
      rw [gidx_succ hp hr hclt, csum_succ]
      have hih := ih (by omega) (by omega)
      omega

/-- The cumulative capacity at the greedy index `+1` reaches `r`. -/
lemma le_csum_gidx_succ {p : ℕ} (hp : 2 ≤ p) : ∀ (r n : ℕ), r ≤ p - 1 →
    r ≤ csum p n (gidx p hp r n + 1) := by
  intro r n
  induction r, n using gidx.induct p hp with
  | case1 n => intro hr; exact Nat.zero_le _
  | case2 r n hr0 hc0 ih =>
      intro hr
      rw [gidx_succ hp hr (by rw [hc0]; omega), csum_succ, hc0, Nat.zero_add]
      exact ih (by omega)
  | case3 r n hr0 hc0 hle =>
      intro hr
      rw [gidx_eq_zero hp hr hle]
      simp [csum]
      exact hle
  | case4 r n hr0 hc0 hnc ih =>
      intro hr
      have hclt : capp p n 0 < r := by omega
      rw [gidx_succ hp hr hclt, csum_succ]
      have ih' := ih (by omega)
      omega

/-- **The closed form of the greedy fill.** -/
theorem Gg_eq_sum {p : ℕ} (hp : 2 ≤ p) (r n : ℕ) (hr : r ≤ p - 1) :
    Gg p hp r n = (∑ i ∈ Finset.range (gidx p hp r n), capp p n i * p ^ i)
      + (r - csum p n (gidx p hp r n)) * p ^ (gidx p hp r n) := by
  induction r, n using Gg.induct p hp with
  | case1 n =>
      rw [Gg.eq_def, if_pos rfl]
      rw [gidx_eq_zero hp (r := 0) (n := n) (by omega) (Nat.zero_le _)]
      simp [csum]
  | case2 r n hr0 hc0 ih =>
      rw [Gg.eq_def, if_neg hr0, if_pos hc0]
      have hsub : r - capp p n 0 = r := by rw [hc0]; omega
      rw [gidx_succ hp hr (by rw [hc0]; omega), hsub, csum_succ, hc0, Nat.zero_add]
      rw [ih hr]
      have hsum : (∑ k ∈ Finset.range (gidx p hp r (n / p) + 1), capp p n k * p ^ k)
          = p * (∑ k ∈ Finset.range (gidx p hp r (n / p)), capp p (n / p) k * p ^ k) := by
        rw [Finset.sum_range_succ']
        rw [Finset.sum_congr rfl (fun i _ =>
          show capp p n (i + 1) * p ^ (i + 1) = p * (capp p (n / p) i * p ^ i) from by
            rw [capp_tail, pow_succ]; ring)]
        rw [← Finset.mul_sum, hc0]
        simp
      have hlast : (r - csum p (n / p) (gidx p hp r (n / p))) * p ^ (gidx p hp r (n / p) + 1)
          = p * ((r - csum p (n / p) (gidx p hp r (n / p))) * p ^ (gidx p hp r (n / p))) := by
        rw [pow_succ]; ring
      rw [hsum, hlast]
      ring
  | case3 r n hr0 hc0 hle =>
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_pos hle]
      rw [gidx_eq_zero hp hr hle]
      simp [csum]
  | case4 r n hr0 hc0 hnc ih =>
      rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_neg hnc]
      have hclt : capp p n 0 < r := by omega
      rw [gidx_succ hp hr hclt]
      rw [csum_succ]
      rw [ih (by omega)]
      rw [Finset.sum_range_succ']
      rw [Finset.sum_congr rfl
        (fun i (_ : i ∈ Finset.range (gidx p hp (r - capp p n 0) (n / p))) =>
        show capp p n (i + 1) * p ^ (i + 1) = p * (capp p (n / p) i * p ^ i) from by
          rw [capp_tail, pow_succ]; ring)]
      rw [← Finset.mul_sum]
      simp only [pow_zero, mul_one]
      rw [pow_succ, Nat.sub_sub]
      ring

end ZagierHoffmanPositiveChar
