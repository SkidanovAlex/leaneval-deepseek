import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog

open Finset Real

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- `t ↦ t^{-10}` is antitone on the positive reals. -/
private lemma rpow_neg10_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-10 : ℝ) ≤ a ^ (-10 : ℝ) :=
  Real.rpow_le_rpow_of_nonpos ha hab (by norm_num)

private lemma rpow_neg_ten (x : ℝ) (hx : 0 < x) : x ^ (-10 : ℝ) = 1 / x ^ 10 := by
  rw [show (-10 : ℝ) = -(10 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hx)]
  rw [show x ^ (10 : ℝ) = x ^ 10 from Real.rpow_natCast x 10]
  rw [one_div]

private lemma div_rpow_ten (C x : ℝ) (hx : 0 < x) :
    C / x ^ (10 : ℝ) = C * x ^ (-10 : ℝ) := by
  rw [show (-10 : ℝ) = -(10 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hx), div_eq_mul_inv]

/-- The sum of `g p - 1/p` over the primes in `[u,v]` equals the difference of the partial
sums of `g` and of `1/p` up to `v` and to `u-1`. -/
private lemma sum_range_prime_eq (g : ℕ → ℝ) {u v : ℕ} (huv : u ≤ v) :
    ∑ p ∈ (Finset.Icc u v).filter Nat.Prime, (g p - (1 : ℝ) / (p : ℝ)) =
      ((∑ p ∈ Nat.primesLE v, g p) - (∑ p ∈ Nat.primesLE (u - 1), g p)) -
        ((∑ p ∈ Nat.primesLE v, (1 : ℝ) / (p : ℝ)) -
          (∑ p ∈ Nat.primesLE (u - 1), (1 : ℝ) / (p : ℝ))) := by
  have hsub : Nat.primesLE (u - 1) ⊆ Nat.primesLE v := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 (by omega), hp.2⟩
  have heq : (Finset.Icc u v).filter Nat.Prime = Nat.primesLE v \ Nat.primesLE (u - 1) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hup, hpv⟩, hpp⟩
      refine ⟨⟨hpv, hpp⟩, fun h => ?_⟩
      have hp2 : 2 ≤ p := hpp.two_le
      omega
    · rintro ⟨⟨hpv, hpp⟩, hnot⟩
      refine ⟨⟨?_, hpv⟩, hpp⟩
      by_contra hlt
      push_neg at hlt
      exact hnot ⟨by omega, hpp⟩
  rw [heq]
  have h1 : ∑ p ∈ Nat.primesLE v, (g p - (1 : ℝ) / (p : ℝ)) =
      (∑ p ∈ Nat.primesLE v, g p) - ∑ p ∈ Nat.primesLE v, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_sub_distrib _ _
  have h2 : ∑ p ∈ Nat.primesLE (u - 1), (g p - (1 : ℝ) / (p : ℝ)) =
      (∑ p ∈ Nat.primesLE (u - 1), g p) - ∑ p ∈ Nat.primesLE (u - 1), (1 : ℝ) / (p : ℝ) :=
    Finset.sum_sub_distrib _ _
  have hsd := Finset.sum_sdiff (s₁ := Nat.primesLE (u - 1)) (s₂ := Nat.primesLE v)
    (f := fun p => g p - (1 : ℝ) / (p : ℝ)) hsub
  rw [h1, h2] at hsd
  linarith [hsd]

/-- For `2 ≤ n ≤ 11` the double logarithm `log log n` is bounded by `10` in absolute value. -/
private lemma loglog_small (n : ℕ) (h2 : 2 ≤ n) (h11 : n ≤ 11) :
    |Real.log (Real.log (n : ℝ))| ≤ 10 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le one_lt_two h2)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hhalf : (1 : ℝ) / 2 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2) (show (2:ℝ) ≤ (n:ℝ) by exact_mod_cast h2)
    have h2' : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hlogle : Real.log (n : ℝ) ≤ 10 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by positivity)
    have hn11 : (n : ℝ) ≤ 11 := by exact_mod_cast h11
    linarith
  have hupper : Real.log (Real.log (n : ℝ)) ≤ 10 := by
    have h := Real.log_le_log hlogpos hlogle
    have h10 : Real.log (10 : ℝ) ≤ 10 := by
      have := Real.log_le_self (show (0 : ℝ) ≤ 10 by norm_num)
      linarith
    linarith
  have hlower : -10 ≤ Real.log (Real.log (n : ℝ)) := by
    have h := Real.log_le_log (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num) hhalf
    have hloghalf : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    have hlog2le1 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    rw [hloghalf] at h
    linarith
  rw [abs_le]
  exact ⟨hlower, hupper⟩

/-- For `n ≤ 10` the reciprocal prime sum is bounded by `12`. -/
private lemma recips_small (n : ℕ) (hn : n ≤ 10) :
    |∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ)| ≤ 12 := by
  have hnonneg : 0 ≤ ∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
  rw [abs_of_nonneg hnonneg]
  have hle : ∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ) ≤ (Nat.primesLE n).card := by
    calc ∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ) ≤ ∑ _p ∈ Nat.primesLE n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpp := Nat.prime_of_mem_primesLE hp
          have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
          rw [div_le_one hppos]
          exact_mod_cast (le_of_lt hpp.one_lt)
      _ = (Nat.primesLE n).card := by simp
  have hcard : (Nat.primesLE n).card ≤ n + 1 := by
    rw [Nat.primesLE_eq_filter_range]
    calc ((Finset.range (n + 1)).filter Nat.Prime).card ≤ (Finset.range (n + 1)).card :=
          Finset.card_filter_le _ _
      _ = n + 1 := Finset.card_range _
  have hcard' : ((Nat.primesLE n).card : ℝ) ≤ 12 := by
    have h : ((Nat.primesLE n).card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
    have : (n : ℝ) ≤ 10 := by exact_mod_cast hn
    linarith
  linarith

/-- Comparison of `(log m)^{-10}` with `(log z)^{-10}` when `z ≤ m + 1` and `11 ≤ m`. -/
private lemma log_comp (z m : ℕ) (hz : 2 ≤ z) (hm : 11 ≤ m) (hzmu : z ≤ m + 1) :
    (Real.log (m : ℝ)) ^ (-10 : ℝ) ≤ 2000 * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by
  have hzpos : 0 < (z : ℝ) := by positivity
  have hz2m : (z : ℝ) ≤ 2 * (m : ℝ) := by
    have h1 : (z : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hzmu
    have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 11) hm)
    linarith
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (lt_of_lt_of_le one_lt_two hz)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (1:ℕ) < 11) hm)
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos hz1
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have hle : Real.log (z : ℝ) ≤ 2 * Real.log (m : ℝ) := by
    have h1 : Real.log (z : ℝ) ≤ Real.log (2 * (m : ℝ)) := Real.log_le_log hzpos hz2m
    have h2 : Real.log (2 * (m : ℝ)) = Real.log 2 + Real.log (m : ℝ) :=
      Real.log_mul (by norm_num) (by positivity)
    have h3 : Real.log (2 : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (le_trans (by norm_num : 2 ≤ 11) hm))
    linarith
  have hmain : (2 * Real.log (m : ℝ)) ^ (-10 : ℝ) ≤ (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
    rpow_neg10_anti hlogz hle
  have hfactor : (2 * Real.log (m : ℝ)) ^ (-10 : ℝ) =
      (1 / 1024) * (Real.log (m : ℝ)) ^ (-10 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hlogm)]
    have h2 : (2 : ℝ) ^ (-10 : ℝ) = 1 / 1024 := by
      rw [rpow_neg_ten (2:ℝ) (by norm_num)]
      norm_num
    rw [h2]
  have hstep : (Real.log (m : ℝ)) ^ (-10 : ℝ) ≤ 1024 * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by
    have h := hmain
    rw [hfactor] at h
    have hz10 : 0 ≤ (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos hlogz (-10))
    linarith
  have hz10 : 0 ≤ (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos hlogz (-10))
  calc (Real.log (m : ℝ)) ^ (-10 : ℝ) ≤ 1024 * (Real.log (z : ℝ)) ^ (-10 : ℝ) := hstep
    _ ≤ 2000 * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by linarith

theorem mertens_range_gap_bound (g : ℕ → ℝ) (c Cs : ℝ)
    (hg_sum : ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE, g p) - (Real.log (Real.log y) + c)| ≤ Cs * (Real.log y) ^ (-10 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z → ∀ u v : ℕ, z ≤ u →
      |∑ p ∈ (Finset.Icc u v).filter Nat.Prime, (g p - 1 / (p : ℝ))| ≤ C * (Real.log z) ^ (-10 : ℝ) := by
  have hCs : 0 ≤ Cs := by
    have h := hg_sum 2 (by norm_num)
    have hpos : 0 < (Real.log 2) ^ (-10 : ℝ) := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) (-10)
    have hnn : 0 ≤ Cs * (Real.log 2) ^ (-10 : ℝ) := le_trans (abs_nonneg _) h
    exact (mul_nonneg_iff_of_pos_right hpos).mp hnn
  obtain ⟨L, Crec, hCrec, hrec⟩ := primeRecips_sub_loglog_powLog 10 (by norm_num)
  set P : ℕ → ℝ := fun n => ∑ p ∈ Nat.primesLE n, g p with hP
  set Q : ℕ → ℝ := fun n => ∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ) with hQ
  have hPf : ∀ n, P n = ∑ p ∈ Nat.primesLE n, g p := fun n => by rw [hP]
  have hQf : ∀ n, Q n = ∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ) := fun n => by rw [hQ]
  have hPbound : ∀ n : ℕ, 2 ≤ n →
      |P n - (Real.log (Real.log (n : ℝ)) + c)| ≤ Cs * (Real.log (n : ℝ)) ^ (-10 : ℝ) := by
    intro n hn
    have h := hg_sum (n : ℝ) (by exact_mod_cast hn)
    rw [Nat.floor_natCast] at h
    simpa only [hPf n] using h
  have hQbound : ∀ n : ℕ, 11 ≤ n →
      |Q n - (Real.log (Real.log (n : ℝ)) + L)| ≤ Crec * (Real.log (n : ℝ)) ^ (-10 : ℝ) := by
    intro n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (1:ℕ) < 11) hn)
    have h := hrec (n : ℝ) (by exact_mod_cast hn)
    rw [Nat.floor_natCast] at h
    rw [div_rpow_ten Crec (Real.log (n : ℝ)) (Real.log_pos hn1)] at h
    have heq : (∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log (n : ℝ)) - L
        = (∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ)) - (Real.log (Real.log (n : ℝ)) + L) := by
      ring
    rw [heq] at h
    simpa only [hQf n] using h
  set β : ℝ := Cs * (Real.log 2) ^ (-10 : ℝ) + Crec * (Real.log 11) ^ (-10 : ℝ)
      + |c - L| + |L| + 40 with hβ
  have hβnonneg : 0 ≤ β := by
    have h1 : 0 ≤ Cs * (Real.log 2) ^ (-10 : ℝ) :=
      mul_nonneg hCs (le_of_lt (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) (-10)))
    have h2 : 0 ≤ Crec * (Real.log 11) ^ (-10 : ℝ) :=
      mul_nonneg (le_of_lt hCrec) (le_of_lt (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) (-10)))
    rw [hβ]; linarith [abs_nonneg (c - L), abs_nonneg L]
  have hDbound : ∀ n : ℕ, |P n - Q n| ≤ β := by
    intro n
    by_cases h1 : n ≤ 1
    · have hPn : P n = 0 := by
        have he : Nat.primesLE n = ∅ := by
          interval_cases n <;> simp [Nat.primesLE_zero, Nat.primesLE_one]
        rw [hPf n, he]; simp
      have hQn : Q n = 0 := by
        have he : Nat.primesLE n = ∅ := by
          interval_cases n <;> simp [Nat.primesLE_zero, Nat.primesLE_one]
        rw [hQf n, he]; simp
      rw [hPn, hQn]
      simpa using hβnonneg
    · push_neg at h1
      have hn2 : 2 ≤ n := h1
      have hD_eq : P n - Q n =
          (P n - (Real.log (Real.log (n : ℝ)) + c)) -
            (Q n - (Real.log (Real.log (n : ℝ)) + L)) + (c - L) := by ring
      rw [hD_eq]
      have hbase : |P n - (Real.log (Real.log (n : ℝ)) + c)|
          + |Q n - (Real.log (Real.log (n : ℝ)) + L)| + |c - L| ≤ β := by
        by_cases h10 : n ≤ 10
        · have hP := hPbound n hn2
          have hQn : |Q n| ≤ 12 := recips_small n h10
          have hLL : |Real.log (Real.log (n : ℝ))| ≤ 10 := loglog_small n hn2 (by omega)
          have hQsplit : |Q n - (Real.log (Real.log (n : ℝ)) + L)|
              ≤ |Q n| + |Real.log (Real.log (n : ℝ))| + |L| := by
            have haux : |Q n + (-(Real.log (Real.log (n : ℝ)) + L))|
                ≤ |Q n| + |-(Real.log (Real.log (n : ℝ)) + L)| := abs_add_le _ _
            rw [abs_neg] at haux
            have h2' : |Real.log (Real.log (n : ℝ)) + L|
                ≤ |Real.log (Real.log (n : ℝ))| + |L| := abs_add_le _ _
            have h3' : Q n - (Real.log (Real.log (n : ℝ)) + L)
                = Q n + (-(Real.log (Real.log (n : ℝ)) + L)) := by ring
            rw [h3']
            linarith
          have hPn : |P n - (Real.log (Real.log (n : ℝ)) + c)|
              ≤ Cs * (Real.log 2) ^ (-10 : ℝ) := by
            have hlogcmp : (Real.log (n : ℝ)) ^ (-10 : ℝ) ≤ (Real.log 2) ^ (-10 : ℝ) :=
              rpow_neg10_anti (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num)
                (by exact_mod_cast hn2))
            calc |P n - (Real.log (Real.log (n : ℝ)) + c)|
                ≤ Cs * (Real.log (n : ℝ)) ^ (-10 : ℝ) := hP
              _ ≤ Cs * (Real.log 2) ^ (-10 : ℝ) := mul_le_mul_of_nonneg_left hlogcmp hCs
          have hmid : |P n - (Real.log (Real.log (n : ℝ)) + c)|
              + |Q n - (Real.log (Real.log (n : ℝ)) + L)| + |c - L|
              ≤ Cs * (Real.log 2) ^ (-10 : ℝ) + (|L| + 30) + |c - L| := by
            linarith [hPn, hQsplit, hQn, hLL]
          have hfin : Cs * (Real.log 2) ^ (-10 : ℝ) + (|L| + 30) + |c - L| ≤ β := by
            rw [hβ]
            have hY : 0 ≤ Crec * (Real.log 11) ^ (-10 : ℝ) :=
              mul_nonneg (le_of_lt hCrec)
                (le_of_lt (Real.rpow_pos_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 11)) (-10)))
            linarith
          linarith [hmid, hfin]
        · push_neg at h10
          have hP := hPbound n hn2
          have hQ := hQbound n h10
          have hPn : |P n - (Real.log (Real.log (n : ℝ)) + c)|
              ≤ Cs * (Real.log 2) ^ (-10 : ℝ) := by
            have hlogcmp : (Real.log (n : ℝ)) ^ (-10 : ℝ) ≤ (Real.log 2) ^ (-10 : ℝ) :=
              rpow_neg10_anti (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num)
                (by exact_mod_cast hn2))
            calc |P n - (Real.log (Real.log (n : ℝ)) + c)|
                ≤ Cs * (Real.log (n : ℝ)) ^ (-10 : ℝ) := hP
              _ ≤ Cs * (Real.log 2) ^ (-10 : ℝ) := mul_le_mul_of_nonneg_left hlogcmp hCs
          have hQn : |Q n - (Real.log (Real.log (n : ℝ)) + L)|
              ≤ Crec * (Real.log 11) ^ (-10 : ℝ) := by
            have hlogcmp : (Real.log (n : ℝ)) ^ (-10 : ℝ) ≤ (Real.log 11) ^ (-10 : ℝ) :=
              rpow_neg10_anti (Real.log_pos (by norm_num : (1:ℝ) < 11)) (Real.log_le_log
                (by norm_num) (by exact_mod_cast h10))
            calc |Q n - (Real.log (Real.log (n : ℝ)) + L)|
                ≤ Crec * (Real.log (n : ℝ)) ^ (-10 : ℝ) := hQ
              _ ≤ Crec * (Real.log 11) ^ (-10 : ℝ) := mul_le_mul_of_nonneg_left hlogcmp (le_of_lt hCrec)
          have hfin : |P n - (Real.log (Real.log (n : ℝ)) + c)|
              + |Q n - (Real.log (Real.log (n : ℝ)) + L)| + |c - L| ≤ β := by
            rw [hβ]; linarith [hPn, hQn, abs_nonneg (c - L), abs_nonneg L]
          exact hfin
      calc |(P n - (Real.log (Real.log (n : ℝ)) + c)) -
              (Q n - (Real.log (Real.log (n : ℝ)) + L)) + (c - L)|
          ≤ |(P n - (Real.log (Real.log (n : ℝ)) + c)) -
              (Q n - (Real.log (Real.log (n : ℝ)) + L))| + |c - L| := abs_add_le _ _
        _ ≤ (|P n - (Real.log (Real.log (n : ℝ)) + c)|
              + |Q n - (Real.log (Real.log (n : ℝ)) + L)|) + |c - L| := by
              have h := abs_sub_le (P n - (Real.log (Real.log (n : ℝ)) + c)) 0
                (Q n - (Real.log (Real.log (n : ℝ)) + L))
              simp only [sub_zero, zero_sub, abs_neg] at h
              linarith
        _ ≤ β := hbase
  set Cfin : ℝ := max (2001 * (Cs + Crec)) (2 * β * (Real.log 11) ^ (10 : ℝ)) + 1 with hCfin
  have hCfin_pos : 0 < Cfin := by
    have h1 : 0 ≤ 2001 * (Cs + Crec) := by nlinarith [hCs, hCrec]
    have h2 : 0 ≤ max (2001 * (Cs + Crec)) (2 * β * (Real.log 11) ^ (10 : ℝ)) :=
      le_max_of_le_left h1
    rw [hCfin]; linarith
  refine ⟨Cfin, hCfin_pos, ?_⟩
  intro z hz u v hzu
  have hlogzpos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hz))
  have hz10nonneg : 0 ≤ (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos hlogzpos (-10))
  by_cases huv : u ≤ v
  · have hsum := sum_range_prime_eq g huv
    rw [← hPf v, ← hPf (u - 1), ← hQf v, ← hQf (u - 1)] at hsum
    rw [hsum]
    by_cases hu : 12 ≤ u
    · have hm11 : 11 ≤ u - 1 := by omega
      have hm2 : 2 ≤ u - 1 := by omega
      have hv11 : 11 ≤ v := by omega
      have hv2 : 2 ≤ v := by omega
      have hPv := hPbound v hv2
      have hPm := hPbound (u - 1) hm2
      have hQv := hQbound v hv11
      have hQm := hQbound (u - 1) hm11
      have hcompv : (Real.log (v : ℝ)) ^ (-10 : ℝ) ≤ (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
        rpow_neg10_anti hlogzpos (Real.log_le_log (by positivity)
          (by exact_mod_cast (le_trans hzu huv)))
      have hcompm : (Real.log ((u - 1 : ℕ) : ℝ)) ^ (-10 : ℝ)
          ≤ 2000 * (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
        log_comp z (u - 1) hz hm11 (by omega)
      have hb1 : |P v - (Real.log (Real.log (v : ℝ)) + c)|
          ≤ Cs * (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
        le_trans hPv (mul_le_mul_of_nonneg_left hcompv hCs)
      have hb2 : |P (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + c)|
          ≤ 2000 * Cs * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by
        calc |P (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + c)|
            ≤ Cs * (Real.log ((u - 1 : ℕ) : ℝ)) ^ (-10 : ℝ) := hPm
          _ ≤ Cs * (2000 * (Real.log (z : ℝ)) ^ (-10 : ℝ)) :=
              mul_le_mul_of_nonneg_left hcompm hCs
          _ = 2000 * Cs * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by ring
      have hb3 : |Q v - (Real.log (Real.log (v : ℝ)) + L)|
          ≤ Crec * (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
        le_trans hQv (mul_le_mul_of_nonneg_left hcompv (le_of_lt hCrec))
      have hb4 : |Q (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + L)|
          ≤ 2000 * Crec * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by
        calc |Q (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + L)|
            ≤ Crec * (Real.log ((u - 1 : ℕ) : ℝ)) ^ (-10 : ℝ) := hQm
          _ ≤ Crec * (2000 * (Real.log (z : ℝ)) ^ (-10 : ℝ)) :=
              mul_le_mul_of_nonneg_left hcompm (le_of_lt hCrec)
          _ = 2000 * Crec * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by ring
      have hdecomp : P v - P (u - 1) - (Q v - Q (u - 1)) =
          (P v - (Real.log (Real.log (v : ℝ)) + c))
            - (P (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + c))
            - (Q v - (Real.log (Real.log (v : ℝ)) + L))
            + (Q (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + L)) := by ring
      rw [hdecomp]
      have htri : |(P v - (Real.log (Real.log (v : ℝ)) + c))
              - (P (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + c))
              - (Q v - (Real.log (Real.log (v : ℝ)) + L))
              + (Q (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + L))|
          ≤ |P v - (Real.log (Real.log (v : ℝ)) + c)|
            + |P (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + c)|
            + |Q v - (Real.log (Real.log (v : ℝ)) + L)|
            + |Q (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + L)| := by
        set A := P v - (Real.log (Real.log (v : ℝ)) + c) with hA
        set B := P (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + c) with hB
        set Cc := Q v - (Real.log (Real.log (v : ℝ)) + L) with hC
        set D := Q (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + L) with hD
        have h1 : |(A - B - Cc) + D| ≤ |A - B - Cc| + |D| := abs_add_le _ _
        have h2 : |A - B - Cc| ≤ |A - B| + |Cc| := by
          have h := abs_sub_le (A - B) 0 Cc; simpa using h
        have h3 : |A - B| ≤ |A| + |B| := by
          have h := abs_sub_le A 0 B; simpa using h
        linarith
      have hbound : |(P v - (Real.log (Real.log (v : ℝ)) + c))
              - (P (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + c))
              - (Q v - (Real.log (Real.log (v : ℝ)) + L))
              + (Q (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + L))|
          ≤ 2001 * (Cs + Crec) * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by
        have hcomb : |P v - (Real.log (Real.log (v : ℝ)) + c)|
              + |P (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + c)|
              + |Q v - (Real.log (Real.log (v : ℝ)) + L)|
              + |Q (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + L)|
            ≤ 2001 * (Cs + Crec) * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by
          have e : 2001 * (Cs + Crec) * (Real.log (z : ℝ)) ^ (-10 : ℝ)
              = Cs * (Real.log (z : ℝ)) ^ (-10 : ℝ)
                + 2000 * Cs * (Real.log (z : ℝ)) ^ (-10 : ℝ)
                + Crec * (Real.log (z : ℝ)) ^ (-10 : ℝ)
                + 2000 * Crec * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by ring
          rw [e]
          linarith [hb1, hb2, hb3, hb4]
        linarith [htri, hcomb]
      have hCfin_ge : 2001 * (Cs + Crec) ≤ Cfin := by
        rw [hCfin]
        have := le_max_left (2001 * (Cs + Crec)) (2 * β * (Real.log 11) ^ (10 : ℝ))
        linarith
      calc |(P v - (Real.log (Real.log (v : ℝ)) + c))
              - (P (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + c))
              - (Q v - (Real.log (Real.log (v : ℝ)) + L))
              + (Q (u - 1) - (Real.log (Real.log ((u - 1 : ℕ) : ℝ)) + L))|
          ≤ 2001 * (Cs + Crec) * (Real.log (z : ℝ)) ^ (-10 : ℝ) := hbound
        _ ≤ Cfin * (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
            mul_le_mul_of_nonneg_right hCfin_ge hz10nonneg
    · push_neg at hu
      have hz11 : z ≤ 11 := le_trans hzu (by omega)
      have hsumD : P v - P (u - 1) - (Q v - Q (u - 1)) = (P v - Q v) - (P (u - 1) - Q (u - 1)) :=
        by ring
      rw [hsumD]
      have hDv := hDbound v
      have hDm := hDbound (u - 1)
      have h2β : |(P v - Q v) - (P (u - 1) - Q (u - 1))| ≤ 2 * β := by
        calc |(P v - Q v) - (P (u - 1) - Q (u - 1))|
            ≤ |P v - Q v| + |P (u - 1) - Q (u - 1)| := by
              have h := abs_sub_le (P v - Q v) 0 (P (u - 1) - Q (u - 1))
              simp only [sub_zero, zero_sub, abs_neg] at h
              linarith
          _ ≤ β + β := add_le_add hDv hDm
          _ = 2 * β := by ring
      have hlogzle11 : Real.log (z : ℝ) ≤ Real.log (11 : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hz11)
      have hat : (1 : ℝ) ≤ Real.log 11 / Real.log (z : ℝ) := by
        rw [le_div_iff₀ hlogzpos]; linarith
      have hkey : 1 ≤ (Real.log 11) ^ (10 : ℝ) * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by
        have hrew : (Real.log 11) ^ (10 : ℝ) * (Real.log (z : ℝ)) ^ (-10 : ℝ)
            = (Real.log 11 / Real.log (z : ℝ)) ^ 10 := by
          rw [show (-10 : ℝ) = -(10 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hlogzpos)]
          rw [show Real.log 11 ^ (10 : ℝ) = Real.log 11 ^ 10 from Real.rpow_natCast _ 10]
          rw [show Real.log (z : ℝ) ^ (10 : ℝ) = Real.log (z : ℝ) ^ 10 from Real.rpow_natCast _ 10]
          rw [div_pow, div_eq_mul_inv]
        rw [hrew]
        exact one_le_pow₀ hat
      have hCf : 2 * β * (Real.log 11) ^ (10 : ℝ) ≤ Cfin := by
        rw [hCfin]
        have := le_max_right (2001 * (Cs + Crec)) (2 * β * (Real.log 11) ^ (10 : ℝ))
        linarith
      have hfinal : 2 * β ≤ Cfin * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by
        have hb0 : 0 ≤ 2 * β := by linarith [hβnonneg]
        have step1 : 2 * β ≤ 2 * β * ((Real.log 11) ^ (10 : ℝ) * (Real.log (z : ℝ)) ^ (-10 : ℝ)) := by
          nlinarith [hkey, hb0]
        have step2 : 2 * β * ((Real.log 11) ^ (10 : ℝ) * (Real.log (z : ℝ)) ^ (-10 : ℝ))
            = (2 * β * (Real.log 11) ^ (10 : ℝ)) * (Real.log (z : ℝ)) ^ (-10 : ℝ) := by ring
        rw [step2] at step1
        calc 2 * β ≤ (2 * β * (Real.log 11) ^ (10 : ℝ)) * (Real.log (z : ℝ)) ^ (-10 : ℝ) := step1
          _ ≤ Cfin * (Real.log (z : ℝ)) ^ (-10 : ℝ) :=
              mul_le_mul_of_nonneg_right hCf hz10nonneg
      linarith [h2β, hfinal]
  · have hempty : (Finset.Icc u v).filter Nat.Prime = ∅ := by
      rw [Finset.Icc_eq_empty (by omega : ¬ u ≤ v)]
      simp
    rw [hempty]
    simp only [Finset.sum_empty, abs_zero]
    exact mul_nonneg (le_of_lt hCfin_pos) hz10nonneg

end

end Commons.NumberTheory.Mertens
