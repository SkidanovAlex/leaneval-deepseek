import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Recursion.defs
import Submission.Work.Recursion.loggrowth
import Submission.Work.Recursion.est1
import Submission.Work.Recursion.est2
import Submission.Work.Recursion.params

/-!
# Area Recursion: Corollary 5.5 and the proof of Theorem 1.1

This file proves `HvdH.RecursionProp`: for every pair of constants `K` (of the main step) and
`Kb` (of the base case) and every threshold `n₁` there are `n₀ ≥ n₁` and `C` such that the
inductive cost bound `CmOf C m = C * (m * size m + 1)` satisfies

* `mainCost K (CmOf C) n + Kb * (n+1) ≤ CmOf C n` for `n ≥ n₀`, and
* `Kb * ((n+1)^2 + n₀.size) ≤ CmOf C n` for `n < n₀`.

The work is split as follows.  `Est1`/`Est2` (`Submission/Work/Recursion/est1.lean`,
`est2.lean`) are the two pure-arithmetic estimates for the two summands of `mainCost`: the
transform term contributes a factor `1 - 1/(2d)` and the resampling term contributes `1/(8d)`.
Here we show that their hypotheses (`Est1Hyp`, `Est2Hyp`) hold for all large `n`, using the §5.1
parameter estimates (`params`) and the log-growth fact `loggrowth`; then we assemble the
constant `C`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Recursion

open HvdH

noncomputable section

/-- Derived form of `loggrowth`: `log₂ log₂ n + 1 ≤ ε (log₂ n)^{1/4}`. -/
lemma loggrowth' (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (1 : ℝ) ≤ Real.logb 2 (n : ℝ) ∧
    Real.logb 2 (Real.logb 2 (n : ℝ)) + 1 ≤ ε * (Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  obtain ⟨N, hN⟩ := loggrowth (max (1 / ε) 1) (lt_max_of_lt_left (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have ht1 : (1 : ℝ) ≤ Real.logb 2 (n : ℝ) := le_trans (le_max_right _ _) h1
  have hlogt : 0 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := Real.logb_nonneg one_lt_two ht1
  refine ⟨ht1, ?_⟩
  have h3 : (1 / ε) * (Real.logb 2 (Real.logb 2 (n : ℝ)) + 1)
      ≤ (Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / 4) :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left (1 / ε) 1) (by linarith)) h2
  have h4 : ε * ((1 / ε) * (Real.logb 2 (Real.logb 2 (n : ℝ)) + 1))
      ≤ ε * (Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left h3 (le_of_lt hε)
  have h5 : ε * ((1 / ε) * (Real.logb 2 (Real.logb 2 (n : ℝ)) + 1))
      = Real.logb 2 (Real.logb 2 (n : ℝ)) + 1 := by
    field_simp
  rwa [h5] at h4

/-- `log₂ log₂ n + 1` is eventually bounded by `ε log₂ n`. -/
lemma log_lin (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Real.logb 2 (Real.logb 2 (n : ℝ)) + 1 ≤ ε * Real.logb 2 (n : ℝ) := by
  obtain ⟨N, hN⟩ := loggrowth' (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have hlogt : 0 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := Real.logb_nonneg one_lt_two h1
  have hpow : (Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / 4) ≤ Real.logb 2 (n : ℝ) := by
    calc (Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / 4)
        ≤ (Real.logb 2 (n : ℝ)) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le h1
          norm_num
      _ = Real.logb 2 (n : ℝ) := Real.rpow_one _
  have hs1 : ε / 2 * (Real.logb 2 (n : ℝ)) ^ ((1 : ℝ) / 4) ≤ ε / 2 * Real.logb 2 (n : ℝ) :=
    mul_le_mul_of_nonneg_left hpow (by linarith)
  have hs2 : ε / 2 * Real.logb 2 (n : ℝ) ≤ ε * Real.logb 2 (n : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- `log₂ n → ∞`. -/
lemma log_large (c : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c ≤ Real.logb 2 (n : ℝ) := by
  obtain ⟨N, hN⟩ := loggrowth (max c 1) (lt_max_of_lt_right zero_lt_one)
  exact ⟨N, fun n hn => le_trans (le_max_left c 1) (hN n hn).1⟩

/-- `log₂ 18 ≤ 5`. -/
lemma logb18_le : Real.logb 2 18 ≤ 5 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
  norm_num

/-- `Est1Hyp` holds for all large `n`. -/
lemma est1hyp_eventually : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Est1Hyp n := by
  obtain ⟨N1, hN1⟩ := log_lin (1 / (3458 * 1728 * 2)) (by norm_num)
  obtain ⟨N2, hN2⟩ := log_large 100000000
  refine ⟨max 2 (max N1 N2), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨⟨hb1, hblin⟩, ⟨hT1, hTp, hTb, hkT⟩, ⟨hrR, hpp⟩, hsz, hsqrt, hapar, hsn, hszle⟩ :=
    params n hn2
  have hkey : 1728 * ((Real.logb 2 (n : ℝ) + 3) / rD + Real.logb 2 (18 * rB n) + 3) + 96
      ≤ (1 - 1 / (2 * rD)) * Real.logb 2 (n : ℝ) := by
    set t := Real.logb 2 (n : ℝ) with ht
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have ht1 : (1 : ℝ) ≤ t := by
      rw [ht, Real.le_logb_iff_rpow_le (b := 2) (x := 1) (y := (n : ℝ)) one_lt_two hnpos]
      have h : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      simpa using h
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hb_le : rB n ≤ 2 * t := by
      have h1 : rB n ≤ t + 1 := by simpa [rB, ht] using hblin
      linarith
    have hrB1 : (1 : ℝ) ≤ rB n := by simpa [rB] using hb1
    have hrBpos : 0 < rB n := lt_of_lt_of_le one_pos hrB1
    have hLle : Real.logb 2 (18 * rB n) ≤ Real.logb 2 18 + (1 + Real.logb 2 t) := by
      calc Real.logb 2 (18 * rB n) = Real.logb 2 18 + Real.logb 2 (rB n) :=
            Real.logb_mul (by norm_num) (ne_of_gt hrBpos)
        _ ≤ Real.logb 2 18 + Real.logb 2 (2 * t) := by
            have h := (Real.logb_le_logb one_lt_two hrBpos (by linarith)).mpr hb_le
            linarith
        _ = Real.logb 2 18 + (1 + Real.logb 2 t) := by
            rw [Real.logb_mul (by norm_num) (ne_of_gt htpos), Real.logb_self_eq_one one_lt_two]
    have hM : Real.logb 2 t + 1 ≤ (1 / (3458 * 1728 * 2)) * t := by
      simpa [ht] using hN1 n hnN1
    have h18 : Real.logb 2 18 ≤ 5 := logb18_le
    have hbig : (100000000 : ℝ) ≤ t := hN2 n hnN2
    have hrd : rD = 1729 := by norm_num [rD, HvdH.D]
    rw [hrd]
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [rB, rR, rT, rS, rK, rD]
  · exact_mod_cast hb1
  · exact_mod_cast hrR
  · exact hTb
  · exact hsz
  · exact hkT
  · exact hsn
  · exact hkey

/-- `log₂ 0`... basic positivity of `rD`. -/
lemma rD_pos : (0 : ℝ) < rD := by norm_num [rD, HvdH.D]

/-- `rD = 1729`. -/
lemma rD_eq : rD = 1729 := by norm_num [rD, HvdH.D]

/-- `Est2Hyp` holds for all large `n` (for `K ≥ 1`). -/
lemma est2hyp_eventually (K : ℕ) (hK : 1 ≤ K) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Est2Hyp K n := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le one_pos hK1
  set A0 : ℝ := (12 * rD ^ 2) ^ ((1 : ℝ) / 4) + 1 with hA0
  have hA0pos : 0 < A0 := by
    rw [hA0]
    have h12 : (0 : ℝ) < 12 * rD ^ 2 := by have h := rD_pos; positivity
    have := Real.rpow_pos_of_pos h12 ((1 : ℝ) / 4)
    linarith
  set C0 : ℝ := 192 * A0 * (K : ℝ) ^ 2 * 2 ^ ((3 : ℝ) / 4) * (Real.logb 2 (6 * (K : ℝ)) + 3)
    with hC0
  have hlog6K : 0 ≤ Real.logb 2 (6 * (K : ℝ)) :=
    Real.logb_nonneg one_lt_two (by nlinarith [hK1])
  have hC0pos : 0 < C0 := by
    rw [hC0]
    have h1 : (0:ℝ) < 192 := by norm_num
    have h2 : (0:ℝ) < 2 ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : (0:ℝ) < Real.logb 2 (6 * (K:ℝ)) + 3 := by linarith
    exact mul_pos (mul_pos (mul_pos (mul_pos h1 hA0pos) (pow_pos hKpos 2)) h2) h3
  obtain ⟨N3, hN3⟩ := loggrowth' (1 / (8 * rD * C0)) (by have := rD_pos; positivity)
  refine ⟨max 2 N3, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnN3 : N3 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨⟨hb1, hblin⟩, ⟨hT1, hTp, hTb, hkT⟩, ⟨hrR, hpp⟩, hsz, hsqrt, hapar, hsn, hszle⟩ :=
    params n hn2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hkey : 192 * A0 * (K : ℝ) ^ 2 * (rB n) ^ ((3 : ℝ) / 4)
      * (Real.logb 2 (6 * (K : ℝ) * rB n) + 2) ≤ (1 / (8 * rD)) * Real.logb 2 (n : ℝ) := by
    set t := Real.logb 2 (n : ℝ) with ht
    set b := rB n with hb
    have ht1 : (1 : ℝ) ≤ t := by
      rw [ht, Real.le_logb_iff_rpow_le (b := 2) (x := 1) (y := (n : ℝ)) one_lt_two hnpos]
      have h : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      simpa using h
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
    have hb1' : (1 : ℝ) ≤ b := by simpa [b, rB] using hb1
    have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1'
    have hb_le : b ≤ 2 * t := by
      have h1 : b ≤ t + 1 := by simpa [b, rB, ht] using hblin
      linarith
    have hb3 : b ^ ((3 : ℝ) / 4) ≤ 2 ^ ((3 : ℝ) / 4) * t ^ ((3 : ℝ) / 4) := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt htpos)]
      exact Real.rpow_le_rpow (le_of_lt hbpos) hb_le (by norm_num)
    have hlog6 : Real.logb 2 (6 * (K : ℝ) * b) + 2
        ≤ (Real.logb 2 (6 * (K : ℝ)) + 3) * (1 + Real.logb 2 t) := by
      have h1 : Real.logb 2 (6 * (K : ℝ) * b) = Real.logb 2 (6 * (K : ℝ)) + Real.logb 2 b :=
        Real.logb_mul (by positivity) (ne_of_gt hbpos)
      have h2 : Real.logb 2 b ≤ 1 + Real.logb 2 t := by
        calc Real.logb 2 b ≤ Real.logb 2 (2 * t) :=
              (Real.logb_le_logb one_lt_two hbpos (by linarith)).mpr hb_le
          _ = 1 + Real.logb 2 t := by
              rw [Real.logb_mul (by norm_num) (ne_of_gt htpos), Real.logb_self_eq_one one_lt_two]
      have h4 : 0 ≤ Real.logb 2 t := Real.logb_nonneg one_lt_two ht1
      nlinarith
    have hgr : t ^ ((3 : ℝ) / 4) * (1 + Real.logb 2 t) ≤ (1 / (8 * rD * C0)) * t := by
      have hN3' := (hN3 n hnN3).2
      rw [← ht] at hN3'
      have h3 : 0 ≤ t ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (le_of_lt htpos) _
      have h := mul_le_mul_of_nonneg_left hN3' h3
      have hpow : t ^ ((3 : ℝ) / 4) * t ^ ((1 : ℝ) / 4) = t := by
        rw [← Real.rpow_add htpos, show (3:ℝ)/4 + 1/4 = 1 by norm_num, Real.rpow_one]
      have heq : t ^ ((3 : ℝ) / 4) * ((1 / (8 * rD * C0)) * t ^ ((1 : ℝ) / 4))
          = (1 / (8 * rD * C0)) * t := by
        calc t ^ ((3:ℝ)/4) * ((1/(8*rD*C0)) * t ^ ((1:ℝ)/4))
            = (1/(8*rD*C0)) * (t ^ ((3:ℝ)/4) * t ^ ((1:ℝ)/4)) := by ring
          _ = (1/(8*rD*C0)) * t := by rw [hpow]
      rw [heq] at h
      linarith
    have hb3nonneg : 0 ≤ b ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (le_of_lt hbpos) _
    have hP : 0 ≤ (Real.logb 2 (6 * (K : ℝ)) + 3) * (1 + Real.logb 2 t) := by
      have h4 : 0 ≤ Real.logb 2 t := Real.logb_nonneg one_lt_two ht1
      nlinarith [hlog6K, h4]
    have hbig : 0 ≤ 192 * A0 * (K : ℝ) ^ 2 := by
      have := rD_pos
      have h := hA0pos
      have h2 := hKpos
      positivity
    calc 192 * A0 * (K : ℝ) ^ 2 * b ^ ((3 : ℝ) / 4)
          * (Real.logb 2 (6 * (K : ℝ) * b) + 2)
        = (192 * A0 * (K : ℝ) ^ 2) * (b ^ ((3 : ℝ) / 4)
            * (Real.logb 2 (6 * (K : ℝ) * b) + 2)) := by ring
      _ ≤ (192 * A0 * (K : ℝ) ^ 2) * ((2 ^ ((3 : ℝ) / 4) * t ^ ((3 : ℝ) / 4))
                * ((Real.logb 2 (6 * (K : ℝ)) + 3) * (1 + Real.logb 2 t))) := by
          apply mul_le_mul_of_nonneg_left _ hbig
          refine mul_le_mul hb3 hlog6 ?_ ?_
          · have h6b : (1 : ℝ) ≤ 6 * (K : ℝ) * b := by
              have h6 : (1 : ℝ) ≤ 6 * (K : ℝ) := by linarith
              calc (1 : ℝ) = 1 * 1 := by ring
                _ ≤ (6 * (K : ℝ)) * b := mul_le_mul h6 hb1' (by norm_num) (by linarith)
            have := Real.logb_nonneg one_lt_two h6b
            linarith
          · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (le_of_lt htpos) _)
      _ = C0 * (t ^ ((3 : ℝ) / 4) * (1 + Real.logb 2 t)) := by
          rw [hC0]; ring
      _ ≤ C0 * ((1 / (8 * rD * C0)) * t) := mul_le_mul_of_nonneg_left hgr (le_of_lt hC0pos)
      _ = (1 / (8 * rD)) * t := by
          field_simp
  have hkey' : 192 * ((12 * rD ^ 2) ^ ((1 : ℝ) / 4) + 1) * (K : ℝ) ^ 2 * (rB n) ^ ((3 : ℝ) / 4)
      * (Real.logb 2 (6 * (K : ℝ) * rB n) + 2) ≤ (1 / (8 * rD)) * Real.logb 2 (n : ℝ) := by
    have h := hkey
    rw [hA0] at h
    exact h
  refine ⟨hK, ?_, ?_, ?_, ?_, ?_, ?_, hkey'⟩ <;> simp only [rB, rT, rS, rQ, rA, rD]
  · exact_mod_cast hb1
  · exact hTb
  · exact hsqrt
  · exact hapar
  · have hm1 : 1 ≤ K * ppar n := by
      have hb2 : 1 ≤ ppar n := by rw [hpp]; omega
      calc (1:ℕ) = 1 * 1 := by ring
        _ ≤ K * ppar n := Nat.mul_le_mul hK hb2
    have h := hszle (K * ppar n) hm1
    simpa [rS, rP] using h
  · exact hsn

/-- `Est1` holds eventually. -/
lemma est1_eventually : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Est1 n := by
  obtain ⟨N, hN⟩ := est1hyp_eventually
  exact ⟨N, fun n hn => est1 n (hN n hn)⟩

/-- `Est2 K` holds eventually. -/
lemma est2_eventually (K : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Est2 K n := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    refine ⟨0, fun n _ => ?_⟩
    simp only [Est2, Nat.cast_zero, zero_mul]
    apply mul_nonneg (div_nonneg zero_le_one (by have := rD_pos; linarith))
    exact mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _)
  · obtain ⟨N, hN⟩ := est2hyp_eventually K hK
    exact ⟨N, fun n hn => est2 K n (hN n hn)⟩


/-- The final assembly: `RecursionProp` from the two estimates. -/
theorem recursion : HvdH.RecursionProp := by
  intro K n₁ Kb
  obtain ⟨N1, hN1⟩ := est1_eventually
  obtain ⟨N2, hN2⟩ := est2_eventually K
  set C0 : ℕ := 4 * HvdH.D * (K + 2 * Kb) + 100 with hC0def
  set n₀ : ℕ := max n₁ (max N1 (max N2 2)) with hn₀def
  set C : ℕ := max C0 (Kb * ((n₀ + 1) ^ 2 + n₀.size) + 1) with hCdef
  refine ⟨n₀, C, le_max_left _ _, ?_⟩
  intro n
  constructor
  · intro hn
    have hn' : n₁ ≤ n ∧ N1 ≤ n ∧ N2 ≤ n ∧ 2 ≤ n := by
      have h := hn
      rw [hn₀def] at h
      simp only [Nat.max_le] at h
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
    have hEst1 : Est1 n := hN1 n hn'.2.1
    have hEst2 : Est2 K n := hN2 n hn'.2.2.1
    have hn2 : 2 ≤ n := hn'.2.2.2
    have hn1 : 1 ≤ n := by omega
    have hn0 : 0 < n := by omega
    have hDpos : (0 : ℝ) < (HvdH.D : ℝ) := by norm_num [HvdH.D]
    have hCpos : 0 < C := by rw [hCdef, hC0def]; omega
    have hC_ge : 4 * HvdH.D * (K + 2 * Kb) ≤ C := by
      rw [hCdef, hC0def]
      exact Nat.le_trans (Nat.le_add_right _ 100) (le_max_left _ _)
    have hmain : (HvdH.mainCost K (HvdH.CmOf C) n : ℝ) + (Kb : ℝ) * ((n : ℝ) + 1)
        ≤ ((HvdH.CmOf C n : ℕ) : ℝ) := by
      have h1 := hEst1
      have h2 := hEst2
      simp only [Est1, Est2, rT, rR, rP, rA, rS, rQ, rD] at h1 h2
      simp only [HvdH.mainCost, HvdH.CmOf]
      push_cast
      set Dr : ℝ := (HvdH.D : ℝ) with hDr
      set Cr : ℝ := (C : ℝ) with hCr
      set Nr : ℝ := (n : ℝ) with hNr
      set Sr : ℝ := (n.size : ℝ) with hSr
      set X1 : ℝ := 3 * (HvdH.rpar n : ℝ) * (HvdH.ppar n : ℝ)
          * ((3 * HvdH.rpar n * HvdH.ppar n).size : ℝ) + 1 with hX1
      set X2 : ℝ := (K : ℝ) * (HvdH.ppar n : ℝ) * ((K * HvdH.ppar n).size : ℝ) + 1 with hX2
      have hDrpos : 0 < Dr := by rw [hDr]; exact hDpos
      have hCrpos : 0 < Cr := by rw [hCr]; exact_mod_cast hCpos
      have hX1nonneg : 0 ≤ X1 := by rw [hX1]; positivity
      have hRpos : (0 : ℝ) < (HvdH.rpar n : ℝ) := by
        have := (params n hn2).2.2.1.1
        exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
      have hdiv : ((HvdH.Tpar n / HvdH.rpar n : ℕ) : ℝ) ≤ (HvdH.Tpar n : ℝ) / (HvdH.rpar n : ℝ) := by
        rw [le_div_iff₀ hRpos]
        have h := Nat.div_mul_le_self (HvdH.Tpar n) (HvdH.rpar n)
        exact_mod_cast h
      have h1' : 12 * ((HvdH.Tpar n / HvdH.rpar n : ℕ) : ℝ) * X1 ≤ (1 - 1 / (2 * Dr)) * (Nr * Sr) := by
        have h12 : 12 * ((HvdH.Tpar n / HvdH.rpar n : ℕ) : ℝ) ≤ 12 * ((HvdH.Tpar n : ℝ) / (HvdH.rpar n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hdiv (by norm_num : (0:ℝ) ≤ 12)
        exact le_trans (mul_le_mul_of_nonneg_right h12 hX1nonneg) h1
      have h1m : 2 * Dr * (12 * ((HvdH.Tpar n / HvdH.rpar n : ℕ) : ℝ) * X1) ≤ (2 * Dr - 1) * (Nr * Sr) := by
        have h := mul_le_mul_of_nonneg_left h1' (by positivity : (0:ℝ) ≤ 2 * Dr)
        have he : (2:ℝ) * Dr * (1 - 1 / (2 * Dr)) = 2 * Dr - 1 := by field_simp
        calc 2 * Dr * (12 * ((HvdH.Tpar n / HvdH.rpar n : ℕ) : ℝ) * X1)
            ≤ 2 * Dr * ((1 - 1 / (2 * Dr)) * (Nr * Sr)) := h
          _ = (2 * Dr - 1) * (Nr * Sr) := by rw [← mul_assoc, he]
      have h2' : (K : ℝ) * (HvdH.Tpar n : ℝ) * ((HvdH.ppar n).sqrt + 1) * (HvdH.apar n : ℝ) * X2
          ≤ (1 / (8 * Dr)) * (Nr * Sr) := h2
      have h2m : 8 * Dr * ((K : ℝ) * (HvdH.Tpar n : ℝ) * ((HvdH.ppar n).sqrt + 1) * (HvdH.apar n : ℝ) * X2)
          ≤ Nr * Sr := by
        have h := mul_le_mul_of_nonneg_left h2' (by positivity : (0:ℝ) ≤ 8 * Dr)
        have he : (8:ℝ) * Dr * (1 / (8 * Dr)) = 1 := by field_simp
        calc 8 * Dr * ((K : ℝ) * (HvdH.Tpar n : ℝ) * ((HvdH.ppar n).sqrt + 1) * (HvdH.apar n : ℝ) * X2)
            ≤ 8 * Dr * ((1 / (8 * Dr)) * (Nr * Sr)) := h
          _ = Nr * Sr := by rw [← mul_assoc, he, one_mul]
      have hTsr1 : (1:ℝ) ≤ Sr := by rw [hSr]; exact_mod_cast Nat.size_pos.mpr hn0
      have hnle : Nr ≤ Nr * Sr := by
        have := mul_le_mul_of_nonneg_left hTsr1 (by positivity : (0:ℝ) ≤ Nr)
        simpa [mul_comm] using this
      have hn1le : Nr + 1 ≤ 2 * (Nr * Sr) := by
        have h : (1:ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast hn1
        nlinarith
      have hCr_ge : 4 * Dr * ((K:ℝ) + 2 * (Kb:ℝ)) ≤ Cr := by
        rw [hCr, hDr]
        exact_mod_cast hC_ge
      have hleft : 4 * Dr * ((K:ℝ) * (Nr * Sr) + (Kb:ℝ) * (Nr + 1)) ≤ Cr * (Nr * Sr) := by
        have hns : (0:ℝ) ≤ Nr * Sr := by positivity
        have hKb0 : (0:ℝ) ≤ (Kb:ℝ) := by positivity
        have hstep : (K:ℝ) * (Nr*Sr) + (Kb:ℝ)*(Nr+1) ≤ ((K:ℝ) + 2*(Kb:ℝ)) * (Nr*Sr) := by
          have h := mul_le_mul_of_nonneg_left hn1le hKb0
          nlinarith [h]
        have hstep2 : 4 * Dr * (((K:ℝ) + 2*(Kb:ℝ)) * (Nr*Sr)) ≤ Cr * (Nr*Sr) := by
          have := mul_le_mul_of_nonneg_right hCr_ge hns
          nlinarith [this]
        calc 4 * Dr * ((K:ℝ) * (Nr * Sr) + (Kb:ℝ) * (Nr + 1))
            ≤ 4 * Dr * (((K:ℝ) + 2*(Kb:ℝ)) * (Nr*Sr)) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ ≤ Cr * (Nr * Sr) := hstep2
      have hT1 : 4 * Dr * (12 * ((HvdH.Tpar n / HvdH.rpar n : ℕ) : ℝ) * (Cr * X1))
          ≤ Cr * ((4 * Dr - 2) * (Nr * Sr)) := by
        have h := mul_le_mul_of_nonneg_left h1m (le_of_lt hCrpos)
        nlinarith [h]
      have hT2 : 4 * Dr * ((K : ℝ) * (HvdH.Tpar n : ℝ) * ((HvdH.ppar n).sqrt + 1)
            * (HvdH.apar n : ℝ) * (Cr * X2)) ≤ Cr * ((1/2 : ℝ) * (Nr * Sr)) := by
        have h := mul_le_mul_of_nonneg_left h2m (le_of_lt hCrpos)
        nlinarith [h]
      have hgoal4 : 4 * Dr * (12 * ((HvdH.Tpar n / HvdH.rpar n : ℕ) : ℝ) * (Cr * X1)
            + (K : ℝ) * (HvdH.Tpar n : ℝ) * ((HvdH.ppar n).sqrt + 1) * (HvdH.apar n : ℝ) * (Cr * X2)
            + (K : ℝ) * Nr * Sr + (Kb : ℝ) * (Nr + 1))
          ≤ 4 * Dr * (Cr * (Nr * Sr + 1)) := by
        have hns : (0:ℝ) ≤ Nr * Sr := by positivity
        nlinarith [hT1, hT2, hleft, hDrpos, hns]
      exact le_of_mul_le_mul_left hgoal4 (by positivity)
    have h5 : ((HvdH.mainCost K (HvdH.CmOf C) n + Kb * (n + 1) : ℕ) : ℝ) ≤ ((HvdH.CmOf C n : ℕ) : ℝ) := by
      push_cast
      linarith
    exact Nat.cast_le.mp h5
  · intro hn
    have h1 : (n + 1) ^ 2 + n₀.size ≤ (n₀ + 1) ^ 2 + n₀.size := by
      have h : n + 1 ≤ n₀ + 1 := by omega
      have h2 : (n+1)^2 ≤ (n₀+1)^2 := Nat.pow_le_pow_left h 2
      omega
    have h2 : Kb * ((n + 1) ^ 2 + n₀.size) ≤ Kb * ((n₀ + 1) ^ 2 + n₀.size) := Nat.mul_le_mul_left Kb h1
    have h3 : Kb * ((n₀ + 1) ^ 2 + n₀.size) ≤ C := by
      have h4 : Kb * ((n₀ + 1) ^ 2 + n₀.size) ≤ Kb * ((n₀ + 1) ^ 2 + n₀.size) + 1 := Nat.le_succ _
      rw [hCdef]
      exact le_trans h4 (le_max_right _ _)
    have h5 : (1 : ℕ) ≤ n * n.size + 1 := by omega
    calc Kb * ((n + 1) ^ 2 + n₀.size) ≤ Kb * ((n₀ + 1) ^ 2 + n₀.size) := h2
      _ ≤ C := h3
      _ = C * 1 := (Nat.mul_one C).symm
      _ ≤ C * (n * n.size + 1) := Nat.mul_le_mul_left C h5

end
end Work.Recursion
