import Mathlib
import Submission.Commons.NumberTheory.Mertens.prodPrime_oneSubInv_ge_half
import Submission.Commons.NumberTheory.Mertens.logDiv_ge_log_sub_sharp
import Submission.Commons.NumberTheory.Mertens.primeRecips_loglog_diff
import Submission.Commons.NumberTheory.Mertens.primeRecips_100_ge_18028
import Submission.Commons.NumberTheory.Mertens.logDiv_100_le_33735
import Submission.Commons.NumberTheory.Mertens.corr_sum_100_ge_3146

set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.Mertens

open Finset Real
open scoped BigOperators

noncomputable section

/-- The Euler product `∏_{p ≤ n} (1 - 1/p)` over the primes `p ≤ n`. -/
private def Psi (n : ℕ) : ℝ := ∏ p ∈ Nat.primesLE n, (1 - 1 / ((p : ℕ) : ℝ))

private lemma Psi_pos (n : ℕ) : 0 < Psi n := by
  unfold Psi
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one hp0]; exact hp1
  linarith

private lemma Psi_antitone : Antitone Psi := by
  intro a b hab
  unfold Psi
  apply Finset.prod_le_prod_of_subset_of_le_one₀
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨le_trans (Nat.mem_primesLE.mp hp).1 hab, (Nat.mem_primesLE.mp hp).2⟩
  · intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have : (1 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; exact hp1
    linarith
  · intro p hp _
    have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith

/-! ## Two numerical facts -/

private lemma log_100_ge : (4.6051701 : ℝ) ≤ Real.log 100 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h5 : (1.6094379123 : ℝ) < Real.log 5 := Real.log_five_gt_d9
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h100 : Real.log (100 : ℝ) = 2 * (Real.log 2 + Real.log 5) := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow, h10]; push_cast; ring
  rw [h100]; linarith

private lemma loglog_100_le : Real.log (Real.log 100) ≤ 1.5275 := by
  have h2u : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h3u : Real.log 3 < (1.0986122888 : ℝ) := Real.log_three_lt_d9
  have h5u : Real.log 5 < (1.6094379126 : ℝ) := Real.log_five_lt_d9
  have h100u : Real.log 100 ≤ 4.6051702 := by
    have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have h100 : Real.log (100 : ℝ) = 2 * (Real.log 2 + Real.log 5) := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow, h10]; push_cast; ring
    rw [h100]; linarith
  have h100p : 0 < Real.log 100 := Real.log_pos (by norm_num)
  have hstep1 : Real.log (Real.log 100) ≤ Real.log 4.6051702 := Real.log_le_log h100p h100u
  have hlog23 : Real.log (23 : ℝ) ≤ 3 * 0.6931471808 + 1.0986122888 - 2 / 47 := by
    have h23 : Real.log (23 : ℝ) = Real.log 24 + Real.log (23 / 24) := by
      rw [← Real.log_mul (by norm_num : (24:ℝ) ≠ 0) (by norm_num : (23/24:ℝ) ≠ 0)]
      norm_num
    have h24 : Real.log (24 : ℝ) = 3 * Real.log 2 + Real.log 3 := by
      rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num,
        Real.log_mul (by norm_num : ((2:ℝ)^3) ≠ 0) (by norm_num : (3:ℝ) ≠ 0), Real.log_pow]
      push_cast; ring
    have h32 : Real.log (23 / 24 : ℝ) ≤ -(2 / 47) := by
      have h24_23 : (23 / 24 : ℝ) = (24 / 23)⁻¹ := by norm_num
      rw [h24_23, Real.log_inv]
      have hlb := Real.le_log_one_add_of_nonneg (x := (1/23:ℝ)) (by norm_num)
      have he : (1 : ℝ) + 1/23 = 24/23 := by norm_num
      rw [he] at hlb
      have h2_47 : (2 : ℝ) * (1/23) / ((1/23) + 2) = 2/47 := by norm_num
      rw [h2_47] at hlb
      linarith
    rw [h23, h24]; linarith
  have h5l : (1.6094379123 : ℝ) < Real.log 5 := Real.log_five_gt_d9
  have hlog46 : Real.log (4.6 : ℝ) ≤ 3 * 0.6931471808 + 1.0986122888 - 2/47 - 1.6094379123 := by
    have h46 : Real.log (4.6 : ℝ) = Real.log 23 - Real.log 5 := by
      rw [show (4.6 : ℝ) = 23 / 5 by norm_num,
        Real.log_div (by norm_num : (23:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
    rw [h46]; linarith
  have hstep2 : Real.log 4.6051702 ≤ 1.5275 := by
    have hsp : (4.6051702 : ℝ) = 4.6 * (1 + (0.0051702 / 4.6)) := by norm_num
    have hlogmul : Real.log 4.6051702 = Real.log 4.6 + Real.log (1 + 0.0051702/4.6) := by
      rw [hsp]
      exact Real.log_mul (x := (4.6:ℝ)) (y := (1 + 0.0051702/4.6 : ℝ))
        (by norm_num) (by norm_num)
    have hsmall : Real.log (1 + 0.0051702/4.6 : ℝ) ≤ 0.0051702/4.6 := by
      have h := Real.log_le_sub_one_of_pos (x := (1 + 0.0051702/4.6 : ℝ)) (by norm_num)
      linarith
    rw [hlogmul]; linarith
  linarith

/-- `log (0.622) ≥ -0.4751`. -/
private lemma log_0622_ge : -(0.4751 : ℝ) ≤ Real.log (0.622 : ℝ) := by
  have h622 : (0.622 : ℝ) = 311 / 500 := by norm_num
  have hinv : (311 / 500 : ℝ) = (500 / 311)⁻¹ := by norm_num
  rw [h622, hinv, Real.log_inv]
  have hfac : (500 / 311 : ℝ) = (8 / 5) * (1 + 3 / 622) := by norm_num
  have hlog : Real.log (500/311 : ℝ) = Real.log (8/5) + Real.log (1 + 3/622) := by
    rw [hfac]
    exact Real.log_mul (x := ((8:ℝ)/5)) (y := (1 + 3/622 : ℝ))
      (by norm_num) (by norm_num)
  have h85 : Real.log ((8 : ℝ)/5) = 3 * Real.log 2 - Real.log 5 := by
    rw [Real.log_div (by norm_num : (8:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0),
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  have h2u : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h5l : (1.6094379123 : ℝ) < Real.log 5 := Real.log_five_gt_d9
  have hsmall : Real.log (1 + 3/622 : ℝ) ≤ 3/622 := by
    have h := Real.log_le_sub_one_of_pos (x := (1 + 3/622 : ℝ)) (by norm_num)
    linarith
  rw [hlog, h85]
  linarith

/-! ## `logRatioSum` decomposed into prime reciprocals and a correction -/

private lemma logRatioSum_eq (x : ℝ) :
    logRatioSum x = primeRecips x + logRatioCorrSum x := by
  simp only [logRatioSum, primeRecips, logRatioCorrSum, corrTerm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

private lemma logRatioCorrSum_mono : Monotone logRatioCorrSum := by
  intro x y hxy
  simp only [logRatioCorrSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 (Nat.floor_mono hxy), hp.2⟩
  · intro p hp _
    exact corrTerm_nonneg (Nat.mem_primesLE.mp hp).2

private lemma logRatioCorrSum_ge_100 (x : ℝ) (hx : 100 ≤ x) :
    (0.3146 : ℝ) ≤ logRatioCorrSum x := by
  have h100 : logRatioCorrSum (100 : ℝ)
      = ∑ p ∈ Nat.primesLE 100, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ)) := by
    unfold logRatioCorrSum
    rw [Nat.floor_ofNat]
    rfl
  have hmono : logRatioCorrSum (100 : ℝ) ≤ logRatioCorrSum x := logRatioCorrSum_mono hx
  have h := corr_sum_100_ge_3146
  rw [h100] at hmono
  linarith

/-! ## The lower bound for `primeRecips x - log log x` -/

private lemma primeRecips_sub_loglog_ge (x : ℝ) (hx : 100 ≤ x) :
    (0.1605 : ℝ) ≤ primeRecips x - Real.log (Real.log x) := by
  have h2x : (2 : ℝ) ≤ 100 := by norm_num
  have hident := primeRecips_loglog_diff (x := (100 : ℝ)) (X := x) (B₁ := -1.76) h2x hx
  have hlog100pos : 0 < Real.log (100 : ℝ) := Real.log_pos (by norm_num)
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsx : 0 ≤ logDiv x - Real.log x + 1.76 := by
    have := logDiv_ge_log_sub_sharp x (by linarith)
    linarith
  have hint : 0 ≤ ∫ t in (100:ℝ)..x,
      (logDiv t - Real.log t - (-1.76)) / (t * (Real.log t) ^ 2) := by
    apply intervalIntegral.integral_nonneg hx
    intro t ht
    rw [Set.mem_Icc] at ht
    have ht2 : (2:ℝ) ≤ t := by linarith [ht.1]
    have ht0 : (0:ℝ) < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hs : 0 ≤ logDiv t - Real.log t - (-1.76) := by
      have := logDiv_ge_log_sub_sharp t ht2
      linarith
    have hden : 0 < t * (Real.log t)^2 := by positivity
    exact div_nonneg hs (le_of_lt hden)
  have hdiv100 : logDiv (100:ℝ) = ∑ p ∈ Nat.primesLE 100, Real.log (p : ℝ) / (p : ℝ) := by
    unfold logDiv
    rw [Nat.floor_ofNat]
  have hdiv100le : logDiv (100:ℝ) ≤ 3.3735 := by
    rw [hdiv100]; exact logDiv_100_le_33735
  have hprec100 : primeRecips (100:ℝ) = ∑ p ∈ Nat.primesLE 100, (1:ℝ) / (p : ℝ) := by
    unfold primeRecips
    rw [Nat.floor_ofNat]
  have hprec100ge : (1.8028 : ℝ) ≤ primeRecips (100:ℝ) := by
    rw [hprec100]; exact primeRecips_100_ge_18028
  have hs100ub : (logDiv (100:ℝ) - Real.log (100:ℝ) + 1.76)/Real.log (100:ℝ) ≤ 0.1147254 := by
    have hlog100ge : (4.6051701:ℝ) ≤ Real.log 100 := log_100_ge
    have hnum : logDiv (100:ℝ) - Real.log (100:ℝ) + 1.76 ≤ 0.5283299 := by linarith
    have h := div_le_div_of_nonneg_right hnum (le_of_lt hlog100pos)
    have h2 : (0.5283299:ℝ)/Real.log 100 ≤ 0.5283299/4.6051701 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog100ge
    have h3 : (0.5283299:ℝ)/4.6051701 ≤ 0.1147254 := by norm_num
    linarith
  have hanchor : (0.2753 : ℝ) ≤ primeRecips (100:ℝ) - Real.log (Real.log (100:ℝ)) := by
    have := loglog_100_le
    linarith
  have hsxterm : 0 ≤ (logDiv x - Real.log x + 1.76)/Real.log x :=
    div_nonneg hsx (le_of_lt hlogxpos)
  -- rewrite hident with `- (-1.76) = + 1.76`
  rw [show (logDiv x - Real.log x - (-1.76)) = (logDiv x - Real.log x + 1.76) by ring,
      show (logDiv (100:ℝ) - Real.log (100:ℝ) - (-1.76))
        = (logDiv (100:ℝ) - Real.log (100:ℝ) + 1.76) by ring] at hident
  linarith [hident, hint, hsxterm, hs100ub, hanchor]

private lemma F_ge (x : ℝ) (hx : 100 ≤ x) :
    (0.4751 : ℝ) ≤ logRatioSum x - Real.log (Real.log x) := by
  have h1 := primeRecips_sub_loglog_ge x hx
  have h2 := logRatioCorrSum_ge_100 x hx
  rw [logRatioSum_eq]
  linarith

private lemma log_Psi_eq (x : ℝ) : Real.log (Psi ⌊x⌋₊) = -logRatioSum x := by
  unfold Psi logRatioSum
  have hne : ∀ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) - 1 / ((p:ℕ):ℝ) ≠ 0 := by
    intro p hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one hp0]; exact hp1
    linarith
  rw [Real.log_prod hne, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h1 : 1 - 1 / ((p:ℕ):ℝ) = (((p : ℝ) / ((p : ℝ) - 1))⁻¹) := by
    field_simp
  rw [h1, Real.log_inv]

/-- For `x ≥ 100`, `∏_{p ≤ x} (1 - 1/p) ≤ 0.622 / log x`. -/
private lemma Psi_le_real (x : ℝ) (hx : 100 ≤ x) :
    Psi ⌊x⌋₊ ≤ 0.622 / Real.log x := by
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hPpos : 0 < Psi ⌊x⌋₊ := Psi_pos _
  have hC : (0 : ℝ) < 0.622 := by norm_num
  have hF := F_ge x hx
  have hlogC := log_0622_ge
  have htarget : Real.log (Psi ⌊x⌋₊) ≤ Real.log (0.622 / Real.log x) := by
    rw [Real.log_div (ne_of_gt hC) (ne_of_gt hlogx), log_Psi_eq]
    linarith
  have h := Real.exp_le_exp.mpr htarget
  rwa [Real.exp_log hPpos, Real.exp_log (div_pos hC hlogx)] at h

/-! ## The main theorem -/

theorem prod_one_sub_inv_range_lower_sharp :
    ∀ P Q : ℝ, 100 ≤ P → P ≤ Q →
      (4/5 : ℝ) * (Real.log P / Real.log Q) ≤
        ∏ p ∈ (Nat.primesLE ⌊Q⌋₊).filter (fun p : ℕ => P ≤ (p : ℝ)),
            (1 - 1 / ((p : ℕ) : ℝ)) := by
  intro P Q hP hPQ
  set M : ℕ := Nat.ceil P with hM
  set N : ℕ := Nat.floor Q with hN
  have hP1 : (1 : ℝ) < P := by linarith
  have hQ1 : (1 : ℝ) < Q := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ1
  have hM100 : 100 ≤ M := by
    have h1 : P ≤ (M : ℝ) := by rw [hM]; exact Nat.le_ceil P
    have h2 : (100 : ℝ) ≤ (M : ℝ) := le_trans hP h1
    exact_mod_cast h2
  have hQle : (N : ℝ) ≤ Q := by rw [hN]; exact Nat.floor_le (by linarith)
  by_cases hMN : M ≤ N
  · have hfilt : (Nat.primesLE N).filter (fun p : ℕ => P ≤ (p : ℝ))
        = (Nat.primesLE N).filter (fun p : ℕ => M ≤ p) := by
      apply Finset.filter_congr
      intro p _
      rw [hM, Nat.ceil_le]
    rw [hfilt]
    have hprodeq : ∏ p ∈ (Nat.primesLE N).filter (fun p : ℕ => M ≤ p),
        (1 - 1 / ((p : ℕ) : ℝ)) = Psi N / Psi (M - 1) := by
      have hsub : Nat.primesLE (M - 1) ⊆ Nat.primesLE N := fun p hp =>
        Nat.mem_primesLE.mpr
          ⟨by have := (Nat.mem_primesLE.mp hp).1; omega, (Nat.mem_primesLE.mp hp).2⟩
      have hset : (Nat.primesLE N).filter (fun p : ℕ => M ≤ p)
          = Nat.primesLE N \ Nat.primesLE (M - 1) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE]
        constructor
        · rintro ⟨⟨hpN, hpp⟩, hMp⟩
          exact ⟨⟨hpN, hpp⟩, fun h => by omega⟩
        · rintro ⟨⟨hpN, hpp⟩, hnot⟩
          exact ⟨⟨hpN, hpp⟩, by by_contra h; push Not at h; exact hnot ⟨by omega, hpp⟩⟩
      rw [hset, eq_div_iff (ne_of_gt (Psi_pos (M - 1)))]
      simp only [Psi]
      exact Finset.prod_sdiff hsub
    rw [hprodeq]
    have hN100 : 100 ≤ N := le_trans hM100 hMN
    have hlow : (1/2 : ℝ) / Real.log (N:ℝ) ≤ Psi N := by
      have := prodPrime_oneSubInv_ge_half N hN100
      simpa [Psi, one_div] using this
    have hN1 : (1:ℝ) < (N:ℝ) := by
      have : (100:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN100
      linarith
    have hlogN : 0 < Real.log (N:ℝ) := Real.log_pos hN1
    have hNpos : 0 < Psi N := Psi_pos N
    have hMge1 : 1 ≤ M := by omega
    -- upper bound at M-1
    have hupp : Psi (M - 1) ≤ 0.622 / Real.log ((M : ℝ) - 1) := by
      rcases Nat.lt_or_ge (M - 1) 100 with hlt | hge
      · have hM99 : M = 100 := by omega
        have hPsi99 : Psi (M - 1) = Psi 100 := by
          have h1 : M - 1 = 99 := by omega
          rw [h1]
          unfold Psi
          rw [show Nat.primesLE 99 = Nat.primesLE 100 from by decide]
        rw [hPsi99]
        have hb := Psi_le_real 100 (by norm_num)
        rw [Nat.floor_ofNat] at hb
        have hlog100 : 0 < Real.log (100:ℝ) := Real.log_pos (by norm_num)
        have hlog99le : Real.log ((99:ℕ):ℝ) ≤ Real.log 100 :=
          Real.log_le_log (by norm_num) (by norm_num)
        have hlog99pos : 0 < Real.log ((99:ℕ):ℝ) := Real.log_pos (by norm_num)
        have hM99r : ((M : ℝ) - 1) = 99 := by rw [hM99]; norm_num
        rw [hM99r]
        calc Psi 100 ≤ 0.622 / Real.log 100 := hb
          _ ≤ 0.622 / Real.log (99:ℝ) :=
              div_le_div_of_nonneg_left (by norm_num) hlog99pos hlog99le
      · have hge100 : (100:ℝ) ≤ (M:ℝ) - 1 := by
          have hMge101 : 101 ≤ M := by omega
          have h : (101:ℝ) ≤ (M:ℝ) := by exact_mod_cast hMge101
          linarith
        have hb := Psi_le_real ((M:ℝ) - 1) hge100
        have hfl : ⌊((M:ℝ) - 1)⌋₊ = M - 1 := by
          rw [show ((M:ℝ) - 1) = ((M - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hMge1]; ring]
          exact Nat.floor_natCast (M - 1)
        rw [hfl] at hb
        exact hb
    have hlogM1pos : 0 < Real.log ((M:ℝ) - 1) := by
      apply Real.log_pos
      have h : (100:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM100
      linarith
    have hPsiMpos : 0 < Psi (M - 1) := Psi_pos _
    -- invert the upper bound
    have hinv : Real.log ((M:ℝ) - 1) / 0.622 ≤ 1 / Psi (M - 1) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 0.622) hPsiMpos]
      have h := hupp
      rw [le_div_iff₀ hlogM1pos] at h
      linarith [h]
    have hratio : (1/2 : ℝ)/Real.log (N:ℝ) * (Real.log ((M:ℝ) - 1)/0.622)
        ≤ Psi N / Psi (M - 1) := by
      have h1 : (1/2 : ℝ)/Real.log (N:ℝ) * (Real.log ((M:ℝ) - 1)/0.622)
          ≤ Psi N * (1/Psi (M - 1)) := by
        apply mul_le_mul hlow hinv (by positivity) (le_of_lt hNpos)
      rwa [mul_one_div] at h1
    -- the two bounds combine to the desired inequality
    have hlogMpos : 0 < Real.log (M:ℝ) := by
      apply Real.log_pos
      have : (100:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM100
      linarith
    have hle1 : Real.log P ≤ Real.log (M:ℝ) :=
      Real.log_le_log (by linarith) (by rw [hM]; exact Nat.le_ceil P)
    have hle2 : Real.log (N:ℝ) ≤ Real.log Q :=
      Real.log_le_log (by positivity) hQle
    have hdiv1 : Real.log P / Real.log Q ≤ Real.log (M:ℝ) / Real.log Q :=
      div_le_div_of_nonneg_right hle1 (le_of_lt hlogQ)
    have hdiv2 : Real.log (M:ℝ) / Real.log Q ≤ Real.log (M:ℝ) / Real.log (N:ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hlogMpos) hlogN hle2
    have hlogMge : (4.6051701:ℝ) ≤ Real.log (M:ℝ) :=
      le_trans log_100_ge (Real.log_le_log (by norm_num) (by exact_mod_cast hM100))
    have hkey : (0.8:ℝ) * Real.log (M:ℝ) ≤ Real.log ((M:ℝ) - 1) / (2*0.622) := by
      have h1 : (1/99:ℝ) ≤ 0.0047989 * Real.log (M:ℝ) := by linarith
      have hlogdiff : Real.log (M:ℝ) - Real.log ((M:ℝ)-1) ≤ 1/99 := by
        have hpos1 : (0:ℝ) < (M:ℝ) := by
          have : (100:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM100
          linarith
        have hpos2 : (0:ℝ) < (M:ℝ)-1 := by
          have h : (100:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM100
          linarith
        rw [← Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2)]
        have h := Real.log_le_sub_one_of_pos (div_pos hpos1 hpos2)
        have heq : (M:ℝ)/((M:ℝ)-1) - 1 = 1/((M:ℝ)-1) := by field_simp; ring
        rw [heq] at h
        have h2 : 1/((M:ℝ)-1) ≤ 1/99 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          have : (100:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM100
          linarith
        linarith [h, h2]
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2*0.622)]
      nlinarith [h1, hlogdiff, hlogMge]
    have h4 : (4/5:ℝ)*(Real.log P/Real.log Q) ≤ (4/5:ℝ)*(Real.log (M:ℝ)/Real.log (N:ℝ)) :=
      mul_le_mul_of_nonneg_left (hdiv1.trans hdiv2) (by norm_num)
    have h5 : (4/5:ℝ)*(Real.log (M:ℝ)/Real.log (N:ℝ))
        ≤ (1/2 : ℝ)/Real.log (N:ℝ) * (Real.log ((M:ℝ) - 1)/0.622) := by
      have heq1 : (4/5:ℝ)*(Real.log (M:ℝ)/Real.log (N:ℝ))
          = ((4/5)*Real.log (M:ℝ))/Real.log (N:ℝ) := by ring
      have heq2 : (1/2 : ℝ)/Real.log (N:ℝ) * (Real.log ((M:ℝ) - 1)/0.622)
          = (Real.log ((M:ℝ) - 1)/(2*0.622))/Real.log (N:ℝ) := by field_simp
      rw [heq1, heq2]
      exact div_le_div_of_nonneg_right (by linarith [hkey]) (le_of_lt hlogN)
    linarith [h4, h5, hratio]
  · -- M > N: empty product
    have hempty : (Nat.primesLE N).filter (fun p : ℕ => P ≤ (p : ℝ)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpN, hpP⟩ := hp
      have hpM : M ≤ p := by rw [hM, Nat.ceil_le]; exact hpP
      have hple : p ≤ N := (Nat.mem_primesLE.mp hpN).1
      omega
    rw [hempty, Finset.prod_empty]
    have hratio : Real.log P / Real.log Q ≤ 1 := by
      rw [div_le_one hlogQ]
      exact Real.log_le_log (by linarith) hPQ
    nlinarith [hratio]

end

end Commons.NumberTheory.Mertens
