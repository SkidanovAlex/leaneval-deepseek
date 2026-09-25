import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.Identity

open Finset

/-! ## Elementary pieces for the `O(1/√x)` bound on the prime tail

`primeTail x = Σ_{p ≤ x} Σ_{k > e_p} 1/(k p^k)` with `e_p = Nat.log p ⌊x⌋₊` the exponent of
`p` in `lcm(1..⌊x⌋₊)`.  The plan (ROUTE_LEAD §3.1 step 5) is

* each summand is a genuine tail of the series `-log (1 - 1/p) = Σ_{k ≥ 1} 1/(k p^k)`, and is
  bounded by `2 / p^{e_p+1}`;
* for `p ≤ √x` this is `≤ 2/x`, and there are at most `√x` such primes;
* for `p > √x` one has `e_p = 1`, so the summand is `≤ 2/p²`, and `Σ_{p > √x} 1/p² ≤ 1/√x`.

The two blocks contribute `2/√x` and `3/√x`. -/

/-- Reindexing `Icc 1 e` onto `range e`. -/
private lemma sum_Icc_one_eq_sum_range (e : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 e, g k = ∑ i ∈ Finset.range e, g (i + 1) := by
  induction e with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Finset.sum_range_succ, ih]

/-- `-log (1 - 1/p) - Σ_{k=1}^{e} 1/(k p^k)` is exactly the tail of the series
`-log (1 - 1/p) = Σ_{k≥1} 1/(k p^k)`. -/
private lemma summand_eq_tail (p : ℕ) (hp : 2 ≤ p) (e : ℕ) :
    -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 e, 1 / ((k : ℝ) * (p : ℝ) ^ k)
      = ∑' k : ℕ, 1 / (((k + e + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + e + 1)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hx : |(1 : ℝ) / (p : ℝ)| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one (by positivity)]
    exact hp1
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one hx
  have hsm : Summable fun n : ℕ => ((1 : ℝ) / (p : ℝ)) ^ (n + 1) / ((n : ℝ) + 1) :=
    hlog.summable
  have htsum : (∑' i : ℕ, ((1 : ℝ) / (p : ℝ)) ^ (i + 1) / ((i : ℝ) + 1))
      = -Real.log (1 - 1 / (p : ℝ)) := hlog.tsum_eq
  have htail : (∑' k : ℕ, ((1 : ℝ) / (p : ℝ)) ^ (k + e + 1) / (((k + e : ℕ) : ℝ) + 1))
      = -Real.log (1 - 1 / (p : ℝ)) - ∑ i ∈ Finset.range e,
          ((1 : ℝ) / (p : ℝ)) ^ (i + 1) / ((i : ℝ) + 1) := by
    have := hsm.sum_add_tsum_nat_add e
    rw [htsum] at this
    linarith
  have hA : -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 e, 1 / ((k : ℝ) * (p : ℝ) ^ k)
      = -Real.log (1 - 1 / (p : ℝ)) - ∑ i ∈ Finset.range e,
          ((1 : ℝ) / (p : ℝ)) ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [sum_Icc_one_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rw [div_pow, one_pow, div_div, mul_comm]
  have hC : (∑' k : ℕ, ((1 : ℝ) / (p : ℝ)) ^ (k + e + 1) / (((k + e : ℕ) : ℝ) + 1))
      = ∑' k : ℕ, 1 / (((k + e + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + e + 1)) := by
    apply tsum_congr
    intro k
    push_cast
    rw [div_pow, one_pow, div_div, mul_comm]
  rw [hA, ← htail, hC]

/-- The tail of `Σ_k 1/((k+e+1) p^{k+e+1})` is `≤ 2/p^{e+1}`. -/
private lemma tail_tsum_le (p : ℕ) (hp : 2 ≤ p) (e : ℕ) :
    ∑' k : ℕ, 1 / (((k + e + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + e + 1))
      ≤ 2 / (p : ℝ) ^ (e + 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  set y : ℝ := (1 : ℝ) / (p : ℝ) with hy
  set c : ℝ := (1 / ((e : ℝ) + 1)) * (1 / (p : ℝ) ^ (e + 1)) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hy_abs : |y| < 1 := by
    rw [hy, abs_of_nonneg (by positivity), div_lt_one hp0]
    exact hp1
  have hsumm_y : Summable fun k : ℕ => y ^ k :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])
  have hsumm_g : Summable fun k : ℕ => c * y ^ k := hsumm_y.mul_left c
  have htsum_g : (∑' k : ℕ, c * y ^ k) = c * (1 - y)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])]
  have hpt : ∀ k : ℕ,
      1 / (((k + e + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + e + 1)) ≤ c * y ^ k := by
    intro k
    have hP : (0 : ℝ) < (p : ℝ) ^ (k + e + 1) := by positivity
    have hAE : (e : ℝ) + 1 ≤ ((k + e + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [show (0 : ℝ) ≤ (k : ℝ) by positivity]
    have hcy : c * y ^ k = 1 / (((e : ℝ) + 1) * (p : ℝ) ^ (k + e + 1)) := by
      have h1 : (p : ℝ) ^ (k + e + 1) = (p : ℝ) ^ (e + 1) * (p : ℝ) ^ k := by
        rw [show k + e + 1 = (e + 1) + k by omega, pow_add]
      rw [hc, hy, div_pow, one_pow, h1]
      field_simp
    rw [hcy]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right hAE (le_of_lt hP))
  have hsumm_f : Summable fun k : ℕ =>
      1 / (((k + e + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + e + 1)) :=
    Summable.of_nonneg_of_le (fun k => by have := hp0; positivity) hpt hsumm_g
  have h2 : (1 - y)⁻¹ ≤ 2 := by
    rw [hy]
    have hpos : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
      rw [sub_pos, div_lt_one hp0]; exact hp1
    have hge : (1 / 2 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
      have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by rw [div_le_iff₀ hp0]; linarith
      linarith
    have := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 1 / 2)).mpr hge
    simpa using this
  calc ∑' k : ℕ, 1 / (((k + e + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + e + 1))
      ≤ ∑' k : ℕ, c * y ^ k := hsumm_f.tsum_le_tsum hpt hsumm_g
    _ = c * (1 - y)⁻¹ := htsum_g
    _ ≤ c * 2 := mul_le_mul_of_nonneg_left h2 (le_of_lt hcpos)
    _ ≤ 2 / (p : ℝ) ^ (e + 1) := by
        rw [hc]
        have hE1 : (1 : ℝ) ≤ (e : ℝ) + 1 := by
          linarith [show (0 : ℝ) ≤ (e : ℝ) by positivity]
        have h1E : (1 : ℝ) / ((e : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact hE1
        have h1P : (0 : ℝ) ≤ 1 / (p : ℝ) ^ (e + 1) := by positivity
        have hstep : (1 / ((e : ℝ) + 1)) * (1 / (p : ℝ) ^ (e + 1)) ≤ 1 / (p : ℝ) ^ (e + 1) := by
          have h := mul_le_mul_of_nonneg_right h1E h1P
          simpa using h
        calc (1 / ((e : ℝ) + 1)) * (1 / (p : ℝ) ^ (e + 1)) * 2
            ≤ (1 / (p : ℝ) ^ (e + 1)) * 2 := by linarith
          _ = 2 / (p : ℝ) ^ (e + 1) := by ring

/-- Per-prime bound: the summand is at most `2/p^{e_p+1}`. -/
private lemma primeTailSummand_le (p : ℕ) (hp : p.Prime) (x : ℝ) :
    Work.RHContract.primeTailSummand p x ≤ 2 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1) := by
  rw [Work.RHContract.primeTailSummand]
  rw [summand_eq_tail p hp.two_le (Nat.log p ⌊x⌋₊)]
  exact tail_tsum_le p hp.two_le _

/-- The telescoping identity `Σ_{i<L} (1/(M+i) - 1/(M+i+1)) = 1/M - 1/(M+L)`. -/
private lemma sum_range_inv_sq_tel (M L : ℕ) :
    ∑ i ∈ Finset.range L, ((1 : ℝ) / ((M : ℝ) + (i : ℝ)) - 1 / ((M : ℝ) + ((i : ℝ) + 1)))
      = 1 / (M : ℝ) - 1 / ((M : ℝ) + (L : ℝ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Telescoping: the sum of `1/j²` over `M+1 ≤ j < K` is at most `1/M`. -/
private lemma sum_Ico_inv_sq_le (M K : ℕ) (hM : 1 ≤ M) :
    ∑ j ∈ Finset.Ico (M + 1) K, 1 / ((j : ℝ) ^ 2) ≤ 1 / (M : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hpt : ∀ k ∈ Finset.range (K - (M + 1)),
      1 / ((((M + 1) + k : ℕ) : ℝ) ^ 2)
        ≤ (1 : ℝ) / ((M : ℝ) + (k : ℝ)) - 1 / ((M : ℝ) + ((k : ℝ) + 1)) := by
    intro k _
    have h1 : (0 : ℝ) < (M : ℝ) + (k : ℝ) := by
      have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
      positivity
    have hkey : (1 : ℝ) / ((M : ℝ) + (k : ℝ)) - 1 / ((M : ℝ) + ((k : ℝ) + 1))
        = 1 / (((M : ℝ) + (k : ℝ)) * ((M : ℝ) + ((k : ℝ) + 1))) := by
      have h2 : (0 : ℝ) < (M : ℝ) + ((k : ℝ) + 1) := by linarith
      field_simp
      ring
    rw [hkey]
    have he : (((M + 1) + k : ℕ) : ℝ) = (M : ℝ) + (k : ℝ) + 1 := by push_cast; ring
    rw [he]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [h1]
  calc ∑ k ∈ Finset.range (K - (M + 1)), 1 / ((((M + 1) + k : ℕ) : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.range (K - (M + 1)),
          ((1 : ℝ) / ((M : ℝ) + (k : ℝ)) - 1 / ((M : ℝ) + ((k : ℝ) + 1))) :=
        Finset.sum_le_sum hpt
    _ = 1 / (M : ℝ) - 1 / ((M : ℝ) + ((K - (M + 1) : ℕ) : ℝ)) := sum_range_inv_sq_tel M (K - (M + 1))
    _ ≤ 1 / (M : ℝ) := by
        have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
        have hnn : (0 : ℝ) ≤ 1 / ((M : ℝ) + ((K - (M + 1) : ℕ) : ℝ)) := by positivity
        linarith

/-- ROUTE_LEAD §3.1 step 5: the prime tail is `O(1/√x)`, with the explicit constant `5`.
Split at `√x`: for `p > √x` one has `e_p = 1` and the summand is `≤ 2/p²`; for `p ≤ √x`,
`p^{e_p+1} > x` gives summand `≤ 2/x`, and there are `≤ √x` such primes. -/
theorem primeTail_le (x : ℝ) (hx : 100 ≤ x) : Work.RHContract.primeTail x ≤ 5 / Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : Real.sqrt x * Real.sqrt x = x := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hx0)
  have hspos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsqrt10 : (10 : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hx0)]
    norm_num
    linarith
  set n : ℕ := ⌊x⌋₊ with hn
  set M : ℕ := ⌊Real.sqrt x⌋₊ with hM
  have hMle : (M : ℝ) ≤ Real.sqrt x := by rw [hM]; exact Nat.floor_le (Real.sqrt_nonneg x)
  have hMlt : Real.sqrt x < (M : ℝ) + 1 := by rw [hM]; exact Nat.lt_floor_add_one _
  have hM10 : 10 ≤ M := by rw [hM]; exact Nat.le_floor (by exact_mod_cast hsqrt10)
  have hnlt : x < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one x
  have hnle : (n : ℝ) ≤ x := by rw [hn]; exact Nat.floor_le (le_of_lt hx0)
  have hn0 : n ≠ 0 := by
    rw [hn]; exact ne_of_gt (Nat.floor_pos.mpr (by linarith))
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  rw [Work.RHContract.primeTail_eq_sum, ← hn]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Nat.primesLE n) (fun p => p ≤ M)
      (fun p => Work.RHContract.primeTailSummand p x)
  rw [← hsplit]
  have hpart1 : ∑ p ∈ (Nat.primesLE n).filter (fun p => p ≤ M),
      Work.RHContract.primeTailSummand p x ≤ 2 / Real.sqrt x := by
    have hb : ∀ p ∈ (Nat.primesLE n).filter (fun p => p ≤ M),
        Work.RHContract.primeTailSummand p x ≤ 2 / x := by
      intro p hp
      have hp' : p ∈ Nat.primesLE n := (Finset.mem_filter.mp hp).1
      have hpp : Nat.Prime p := Nat.prime_of_mem_primesLE hp'
      have hbase := primeTailSummand_le p hpp x
      have hlt : n < p ^ (Nat.log p n + 1) := by
        have h := Nat.lt_pow_succ_log_self hpp.one_lt n
        rwa [Nat.succ_eq_add_one] at h
      have hxlt : x < (p : ℝ) ^ (Nat.log p n + 1) := by
        have h1 : (n : ℝ) + 1 ≤ (p : ℝ) ^ (Nat.log p n + 1) := by
          have h2 := Nat.lt_iff_add_one_le.mp hlt
          exact_mod_cast h2
        linarith
      have h2 : 2 / (p : ℝ) ^ (Nat.log p n + 1) ≤ 2 / x := by
        have h := one_div_le_one_div_of_le hx0 (le_of_lt hxlt)
        have h3 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
        rwa [mul_one_div, mul_one_div] at h3
      linarith
    calc ∑ p ∈ (Nat.primesLE n).filter (fun p => p ≤ M), Work.RHContract.primeTailSummand p x
        ≤ ∑ p ∈ (Nat.primesLE n).filter (fun p => p ≤ M), 2 / x := Finset.sum_le_sum hb
      _ = (((Nat.primesLE n).filter (fun p => p ≤ M)).card : ℝ) * (2 / x) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * (2 / x) := by
          have hcard : ((Nat.primesLE n).filter (fun p => p ≤ M)).card ≤ M := by
            have hsub : (Nat.primesLE n).filter (fun p => p ≤ M) ⊆ Finset.Ioc 1 M := by
              intro p hp
              obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
              exact Finset.mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesLE hp1).one_lt, hp2⟩
            calc ((Nat.primesLE n).filter (fun p => p ≤ M)).card
                ≤ (Finset.Ioc 1 M).card := Finset.card_le_card hsub
              _ = M - 1 := Nat.card_Ioc 1 M
              _ ≤ M := by omega
          have hcard' : (((Nat.primesLE n).filter (fun p => p ≤ M)).card : ℝ) ≤ (M : ℝ) := by
            exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ ≤ 2 / Real.sqrt x := by
          calc (M : ℝ) * (2 / x) ≤ Real.sqrt x * (2 / x) :=
                mul_le_mul_of_nonneg_right hMle (by positivity)
            _ = 2 / Real.sqrt x := by
                field_simp
                linarith [hsq]
  have hpart2 : ∑ p ∈ (Nat.primesLE n).filter (fun p => ¬ p ≤ M),
      Work.RHContract.primeTailSummand p x ≤ 3 / Real.sqrt x := by
    have hb : ∀ p ∈ (Nat.primesLE n).filter (fun p => ¬ p ≤ M),
        Work.RHContract.primeTailSummand p x ≤ 2 / (p : ℝ) ^ 2 := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primesLE hp1
      have hple : p ≤ n := Nat.le_of_mem_primesLE hp1
      have hMp : M < p := not_le.mp hp2
      have hpsqrt : Real.sqrt x < (p : ℝ) := by
        have h1 : (M : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast (by omega : M + 1 ≤ p)
        linarith
      have hxp2 : x < (p : ℝ) ^ 2 := by nlinarith [hpsqrt, hsq, Real.sqrt_nonneg x]
      have hnlt2 : n < p ^ 2 := by
        have h : (n : ℝ) < ((p ^ 2 : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast h
      have hlog1 : Nat.log p n = 1 := by
        have h1 : 1 ≤ Nat.log p n := by
          apply Nat.le_log_of_pow_le hpp.one_lt
          simpa using hple
        have h2 : Nat.log p n < 2 := (Nat.log_lt_iff_lt_pow hpp.one_lt hn0).mpr hnlt2
        omega
      have hbase := primeTailSummand_le p hpp x
      rw [hlog1] at hbase
      simpa using hbase
    calc ∑ p ∈ (Nat.primesLE n).filter (fun p => ¬ p ≤ M), Work.RHContract.primeTailSummand p x
        ≤ ∑ p ∈ (Nat.primesLE n).filter (fun p => ¬ p ≤ M), 2 / (p : ℝ) ^ 2 :=
          Finset.sum_le_sum hb
      _ ≤ ∑ j ∈ Finset.Ico (M + 1) (n + 1), 2 / (j : ℝ) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
            have hple : p ≤ n := Nat.le_of_mem_primesLE hp1
            have hMp : M < p := not_le.mp hp2
            exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          · intro j _ _
            positivity
      _ = 2 * ∑ j ∈ Finset.Ico (M + 1) (n + 1), 1 / (j : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_one_div]
      _ ≤ 2 * (1 / (M : ℝ)) := by
          have h := sum_Ico_inv_sq_le M (n + 1) (by omega : 1 ≤ M)
          linarith
      _ = 2 / (M : ℝ) := by ring
      _ ≤ 3 / Real.sqrt x := by
          have hM23 : (2 : ℝ) / 3 * Real.sqrt x ≤ (M : ℝ) := by
            have h1 : Real.sqrt x - 1 < (M : ℝ) := by linarith
            have h2 : (2 : ℝ) / 3 * Real.sqrt x ≤ Real.sqrt x - 1 := by linarith
            linarith
          rw [div_le_iff₀ hMpos, div_mul_eq_mul_div, le_div_iff₀ hspos]
          nlinarith [hM23]
  have hsum : 2 / Real.sqrt x + 3 / Real.sqrt x = 5 / Real.sqrt x := by ring
  linarith [hpart1, hpart2, hsum]

end Work.RHContract.Identity
