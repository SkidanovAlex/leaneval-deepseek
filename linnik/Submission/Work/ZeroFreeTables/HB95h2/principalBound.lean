import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.zetaLogDeriv_pole_split
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le
import Submission.Work.ZeroFreeTables.Table4.zetaSmoothBound
import Submission.Work.ZeroFreeTables.Table4.eulerFactorBound
import Submission.Work.ZeroFreeTables.Table4.logDerivPrincipalDecomp
import Submission.Work.ZeroFreeTables.Table4.principalArith
import Submission.Work.ZeroFreeTables.Table4.principal_bound

open DirichletCharacter Complex
open scoped BigOperators

namespace Work.ZeroFreeTables.HB95h2

private lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  exact Real.exp_one_lt_three

/-- The three prime sums attached to `q` are bounded by powers of `log L + 2` as soon as
`log q ≤ L` and `L ≥ 1`. -/
private theorem primeSums_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (L : ℝ), 1 ≤ q → 1 ≤ L → Real.log (q : ℝ) ≤ L →
      (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) ≤ C * (Real.log L + 2) ^ 2)
      ∧ (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) ≤ C * (Real.log L + 2) ^ 3)
      ∧ (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) ≤ C * (Real.log L + 2) ^ 4) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨C2, hC2pos, hC2⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨C3, hC3pos, hC3⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  refine ⟨max 1 (max C1 (max C2 C3)), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  intro q L hq1 hL1 hlog
  have hCge1 : (1 : ℝ) ≤ max 1 (max C1 (max C2 C3)) := le_max_left _ _
  have hC1le : C1 ≤ max 1 (max C1 (max C2 C3)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hC2le : C2 ≤ max 1 (max C1 (max C2 C3)) :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hC3le : C3 ≤ max 1 (max C1 (max C2 C3)) :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hbase2 : (0 : ℝ) ≤ Real.log L + 2 := by
    have : 0 ≤ Real.log L := Real.log_nonneg hL1
    linarith only [this]
  rcases lt_or_ge q 3 with hq3 | hq3
  · -- `q ≤ 2`: only the prime `2` can occur
    have hsub : q.primeFactors ⊆ ({2} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_singleton]
      have hpp := (Nat.mem_primeFactors.mp hp).1
      have hpq := (Nat.mem_primeFactors.mp hp).2.1
      have hpq' : p ≤ q := Nat.le_of_dvd (by omega) hpq
      have h2 := hpp.two_le
      omega
    have key : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
        (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ))
          ≤ (max 1 (max C1 (max C2 C3))) * (Real.log L + 2) ^ (j + 1) := by
      intro j hj1 hj3
      have hsumle : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ))
          ≤ (Real.log 2) ^ j / 2 := by
        calc (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ))
            ≤ ∑ p ∈ ({2} : Finset ℕ), (Real.log (p : ℝ)) ^ j / (p : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
                rw [Finset.mem_singleton] at hp
                subst hp
                exact div_nonneg (pow_nonneg (Real.log_nonneg (by norm_num)) j) (by norm_num))
          _ = (Real.log 2) ^ j / 2 := by simp
      have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlog2le1 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith only [this]
      have hnum : (Real.log 2) ^ j ≤ 1 := pow_le_one₀ hlog2nn hlog2le1
      have hhalf : (Real.log 2) ^ j / 2 ≤ 1 := by linarith only [hnum]
      have hpow1 : (1 : ℝ) ≤ (Real.log L + 2) ^ (j + 1) :=
        one_le_pow₀ (by have := Real.log_nonneg hL1; linarith only [this])
      have hCge1' : (0 : ℝ) ≤ max 1 (max C1 (max C2 C3)) := le_trans zero_le_one hCge1
      calc (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ))
          ≤ (Real.log 2) ^ j / 2 := hsumle
        _ ≤ 1 := hhalf
        _ = 1 * 1 := (one_mul 1).symm
        _ ≤ (max 1 (max C1 (max C2 C3))) * (Real.log L + 2) ^ (j + 1) :=
            mul_le_mul hCge1 hpow1 zero_le_one hCge1'
    exact ⟨by simpa using key 1 le_rfl (by norm_num),
           by simpa using key 2 (by norm_num) (by norm_num),
           by simpa using key 3 (by norm_num) le_rfl⟩
  · -- `q ≥ 3`
    have hq3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have hlogq1 : (1 : ℝ) < Real.log (q : ℝ) :=
      lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hq3R)
    have hlogqpos : 0 < Real.log (q : ℝ) := lt_trans zero_lt_one hlogq1
    have hllq_nn : 0 ≤ Real.log (Real.log (q : ℝ)) := Real.log_nonneg hlogq1.le
    have hllq_le : Real.log (Real.log (q : ℝ)) ≤ Real.log L + 2 := by
      have h := Real.log_le_log hlogqpos hlog
      linarith only [h]
    refine ⟨?_, ?_, ?_⟩
    · have h : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
          ≤ C1 * (Real.log (Real.log (q : ℝ))) ^ (1 + 1) := by
        simpa [pow_one] using hC1 q hq3
      have hpow : (Real.log (Real.log (q : ℝ))) ^ (1 + 1) ≤ (Real.log L + 2) ^ 2 := by
        simpa using pow_le_pow_left₀ hllq_nn hllq_le 2
      have h1 : C1 * (Real.log (Real.log (q : ℝ))) ^ (1 + 1) ≤ C1 * (Real.log L + 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hpow hC1pos.le
      have h2 : C1 * (Real.log L + 2) ^ 2
          ≤ (max 1 (max C1 (max C2 C3))) * (Real.log L + 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hC1le (pow_nonneg hbase2 2)
      exact le_trans h (le_trans h1 h2)
    · have h : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
          ≤ C2 * (Real.log (Real.log (q : ℝ))) ^ (2 + 1) := hC2 q hq3
      have hpow : (Real.log (Real.log (q : ℝ))) ^ (2 + 1) ≤ (Real.log L + 2) ^ 3 := by
        simpa using pow_le_pow_left₀ hllq_nn hllq_le 3
      have h1 : C2 * (Real.log (Real.log (q : ℝ))) ^ (2 + 1) ≤ C2 * (Real.log L + 2) ^ 3 :=
        mul_le_mul_of_nonneg_left hpow hC2pos.le
      have h2 : C2 * (Real.log L + 2) ^ 3
          ≤ (max 1 (max C1 (max C2 C3))) * (Real.log L + 2) ^ 3 :=
        mul_le_mul_of_nonneg_right hC2le (pow_nonneg hbase2 3)
      exact le_trans h (le_trans h1 h2)
    · have h : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
          ≤ C3 * (Real.log (Real.log (q : ℝ))) ^ (3 + 1) := hC3 q hq3
      have hpow : (Real.log (Real.log (q : ℝ))) ^ (3 + 1) ≤ (Real.log L + 2) ^ 4 := by
        simpa using pow_le_pow_left₀ hllq_nn hllq_le 4
      have h1 : C3 * (Real.log (Real.log (q : ℝ))) ^ (3 + 1) ≤ C3 * (Real.log L + 2) ^ 4 :=
        mul_le_mul_of_nonneg_left hpow hC3pos.le
      have h2 : C3 * (Real.log L + 2) ^ 4
          ≤ (max 1 (max C1 (max C2 C3))) * (Real.log L + 2) ^ 4 :=
        mul_le_mul_of_nonneg_right hC3le (pow_nonneg hbase2 4)
      exact le_trans h (le_trans h1 h2)

theorem principalBound {a e M : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {q : ℕ} [NeZero q] {L lam₁ : ℝ}, L₀ ≤ L → Real.log (q : ℝ) ≤ L →
      0 ≤ lam₁ → lam₁ ≤ M →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 4 →
        Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
          ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + (a + lam₁) * e := by
  rcases lt_or_ge M 0 with hMneg | hMge
  · refine ⟨0, ?_⟩
    intro q hqne L lam₁ hL0 hlog hlam0 hlamM s hsre him
    exact absurd (by linarith only [hMneg, hlam0, hlamM] : lam₁ < 0) (not_lt.mpr hlam0)
  obtain ⟨M0, hM0pos, hzB⟩ := Work.ZeroFreeTables.Table4.zetaSmoothBound
  obtain ⟨C0, hC0pos, hC0⟩ := primeSums_bound
  obtain ⟨L0, hL01, hL0arith⟩ :=
    Work.ZeroFreeTables.Table4.principalArith M0 C0 (a + M) e hM0pos hC0pos (by linarith only [ha, hMge]) he
  refine ⟨max (max L0 2) (3 * a), ?_⟩
  intro q hqne L lam₁ hL0' hlog hlam0 hlamM s hsre him
  haveI : NeZero q := hqne
  have hL0le : L0 ≤ L := le_trans (le_trans (le_max_left L0 2) (le_max_left _ _)) hL0'
  have hL2 : (2 : ℝ) ≤ L := le_trans (le_trans (le_max_right L0 2) (le_max_left _ _)) hL0'
  have hL3a : 3 * a ≤ L := le_trans (le_max_right _ _) hL0'
  have hLpos : (0 : ℝ) < L := by linarith only [ha, hL3a]
  have hL1 : (1 : ℝ) ≤ L := by linarith only [ha, hL2, hL3a]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hsre1 : 1 < s.re := by
    rw [hsre]
    have : 0 < a / L := div_pos ha hLpos
    linarith only [this]
  have hsre4 : s.re ≤ 4 := by
    rw [hsre]
    have h1 : a / L ≤ 1 / 3 := by rw [div_le_iff₀ hLpos]; linarith only [hL3a]
    linarith only [h1]
  have him5 : |s.im| ≤ 5 := by linarith only [him]
  obtain ⟨hz0, hz1, hz2⟩ := hzB s hsre1 hsre4 him5
  obtain ⟨hE0, hE1, hE2⟩ := Work.ZeroFreeTables.Table4.eulerFactorBound q (le_of_lt hsre1)
  obtain ⟨hS1raw, hS2raw, hS3raw⟩ := hC0 q L hq1 hL1 hlog
  set Rf : ℂ → ℂ := fun z => ∑ p ∈ q.primeFactors,
    (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1) with hRfdef
  set S1 : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hS1def
  set S2 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hS2def
  set S3 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hS3def
  have hE0sum : (∑ p ∈ q.primeFactors, 2 * Real.log (p : ℝ) / (p : ℝ)) = 2 * S1 := by
    rw [hS1def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp; ring
  have hE1sum : (∑ p ∈ q.primeFactors, 4 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) = 4 * S2 := by
    rw [hS2def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp; ring
  have hE2sum : (∑ p ∈ q.primeFactors, 16 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) = 16 * S3 := by
    rw [hS3def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp; ring
  have hES1 : ‖Rf s‖ ≤ 2 * S1 := by rw [← hE0sum, hRfdef]; simpa using hE0
  have hES2 : ‖iteratedDeriv 1 Rf s‖ ≤ 4 * S2 := by rw [← hE1sum]; simpa using hE1
  have hES3 : ‖iteratedDeriv 2 Rf s‖ ≤ 16 * S3 := by rw [← hE2sum]; exact hE2
  have hS1b : S1 ≤ C0 * (Real.log L + 2) ^ 2 := by rw [hS1def]; exact hS1raw
  have hS2b : S2 ≤ C0 * (Real.log L + 2) ^ 3 := by rw [hS2def]; exact hS2raw
  have hS3b : S3 ≤ C0 * (Real.log L + 2) ^ 4 := by rw [hS3def]; exact hS3raw
  have hlog0 : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
      = logDeriv riemannZeta s + Rf s := by
    have hd0 := Work.ZeroFreeTables.Table4.logDerivPrincipalDecomp q 0 (by norm_num) hsre1
    rw [← hRfdef] at hd0
    simpa [iteratedDeriv_zero] using hd0
  have hlog1 : iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
      = iteratedDeriv 1 (logDeriv riemannZeta) s + iteratedDeriv 1 Rf s := by
    have hd1 := Work.ZeroFreeTables.Table4.logDerivPrincipalDecomp q 1 (by norm_num) hsre1
    rw [← hRfdef] at hd1
    exact hd1
  have hlog2 : iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
      = iteratedDeriv 2 (logDeriv riemannZeta) s + iteratedDeriv 2 Rf s := by
    have hd2 := Work.ZeroFreeTables.Table4.logDerivPrincipalDecomp q 2 (by norm_num) hsre1
    rw [← hRfdef] at hd2
    exact hd2
  have hsq : (1 / (s - 1)) ^ 2 = 1 / (s - 1) ^ 2 := by rw [div_pow, one_pow]
  have hcu : (1 / (s - 1)) ^ 3 = 1 / (s - 1) ^ 3 := by rw [div_pow, one_pow]
  have hz1' : |(iteratedDeriv 1 (logDeriv riemannZeta) s - (1 / (s - 1)) ^ 2).re| ≤ M0 := by
    rw [hsq]; exact hz1
  have hz2' : |(iteratedDeriv 2 (logDeriv riemannZeta) s + 2 * (1 / (s - 1)) ^ 3).re| ≤ M0 := by
    have e : 2 * (1 / (s - 1)) ^ 3 = 2 / (s - 1) ^ 3 := by rw [hcu]; ring
    rw [e]; exact hz2
  set A1 : ℝ := (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s).re
      + (1 / (s - 1)).re with hA1def
  set A2 : ℝ := (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s).re
      - ((1 / (s - 1)) ^ 2).re with hA2def
  set A3 : ℝ := (iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s).re
      + 2 * ((1 / (s - 1)) ^ 3).re with hA3def
  have hA1 : |A1| ≤ M0 + 2 * S1 := by
    have h1 : A1 = (logDeriv riemannZeta s + 1 / (s - 1)).re + (Rf s).re := by
      rw [hA1def, hlog0]
      simp only [Complex.add_re]
      ring
    rw [h1]
    have hr : |(Rf s).re| ≤ 2 * S1 := by
      have := Complex.abs_re_le_norm (Rf s)
      linarith only [hES1, hE0, hE0sum, this]
    calc |(logDeriv riemannZeta s + 1 / (s - 1)).re + (Rf s).re|
        ≤ |(logDeriv riemannZeta s + 1 / (s - 1)).re| + |(Rf s).re| := abs_add_le _ _
      _ ≤ M0 + 2 * S1 := by linarith only [hz0, hr]
  have hA2 : |A2| ≤ M0 + 4 * S2 := by
    have h1 : A2 = (iteratedDeriv 1 (logDeriv riemannZeta) s - (1 / (s - 1)) ^ 2).re
        + (iteratedDeriv 1 Rf s).re := by
      rw [hA2def, hlog1]
      simp only [Complex.add_re, Complex.sub_re]
      ring
    rw [h1]
    have hr : |(iteratedDeriv 1 Rf s).re| ≤ 4 * S2 := by
      have := Complex.abs_re_le_norm (iteratedDeriv 1 Rf s)
      linarith only [hES2, hE1, hE1sum, this]
    calc |(iteratedDeriv 1 (logDeriv riemannZeta) s - (1 / (s - 1)) ^ 2).re
            + (iteratedDeriv 1 Rf s).re|
        ≤ |(iteratedDeriv 1 (logDeriv riemannZeta) s - (1 / (s - 1)) ^ 2).re|
            + |(iteratedDeriv 1 Rf s).re| := abs_add_le _ _
      _ ≤ M0 + 4 * S2 := by linarith only [hz1', hr]
  have e2c : ((2 : ℂ) * (1 / (s - 1)) ^ 3).re = 2 * ((1 / (s - 1)) ^ 3).re := by
    rw [Complex.mul_re]; simp
  have hA3 : |A3| ≤ M0 + 16 * S3 := by
    have h1 : A3 = (iteratedDeriv 2 (logDeriv riemannZeta) s + 2 * (1 / (s - 1)) ^ 3).re
        + (iteratedDeriv 2 Rf s).re := by
      rw [hA3def, hlog2]
      simp only [Complex.add_re]
      rw [e2c]
      ring
    rw [h1]
    have hr : |(iteratedDeriv 2 Rf s).re| ≤ 16 * S3 := by
      have := Complex.abs_re_le_norm (iteratedDeriv 2 Rf s)
      linarith only [hES3, hE2, hE2sum, this]
    calc |(iteratedDeriv 2 (logDeriv riemannZeta) s + 2 * (1 / (s - 1)) ^ 3).re
            + (iteratedDeriv 2 Rf s).re|
        ≤ |(iteratedDeriv 2 (logDeriv riemannZeta) s + 2 * (1 / (s - 1)) ^ 3).re|
            + |(iteratedDeriv 2 Rf s).re| := abs_add_le _ _
      _ ≤ M0 + 16 * S3 := by linarith only [hz2', hr]
  have hsig := Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs
    (1 : DirichletCharacter ℂ q) hsre1 a lam₁ L
  have hP3 : (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
      = ((a + lam₁) / L) * (1 / (s - 1)).re + ((a + lam₁) / L) ^ 2 * ((1 / (s - 1)) ^ 2).re
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((1 / (s - 1)) ^ 3).re := by
    rw [Work.ZeroFreeTables.P9.P3_arg_eq a lam₁ L s 1, Work.ZeroFreeTables.P9.P3_re_mul_inv]
  have hsigA : Work.ZeroFreeTables.SigmaP3L q L 1 s a lam₁
      = (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
        + (-((a + lam₁) / L) * A1 + ((a + lam₁) / L) ^ 2 * A2
            - (1 / 3) * ((a + lam₁) / L) ^ 3 * A3) := by
    rw [hsig, hP3]
    simp only [hA1def, hA2def, hA3def]
    ring
  have hfin : -((a + lam₁) / L) * A1 + ((a + lam₁) / L) ^ 2 * A2
      - (1 / 3) * ((a + lam₁) / L) ^ 3 * A3 ≤ (a + lam₁) * e := by
    have hc0 : 0 ≤ (a + lam₁) / L := div_nonneg (by linarith only [ha, hlam0]) (le_of_lt hLpos)
    have h1 : -((a + lam₁) / L) * A1 ≤ ((a + lam₁) / L) * |A1| := by
      have h := mul_le_mul_of_nonneg_left (neg_le_abs A1) hc0
      rw [show -((a + lam₁) / L) * A1 = ((a + lam₁) / L) * (-A1) from by ring]
      exact h
    have h2 : ((a + lam₁) / L) ^ 2 * A2 ≤ ((a + lam₁) / L) ^ 2 * |A2| :=
      mul_le_mul_of_nonneg_left (le_abs_self A2) (pow_nonneg hc0 2)
    have h3 : -((1 / 3) * ((a + lam₁) / L) ^ 3 * A3)
        ≤ (1 / 3) * ((a + lam₁) / L) ^ 3 * |A3| := by
      have hd0 : 0 ≤ (1 / 3) * ((a + lam₁) / L) ^ 3 :=
        mul_nonneg (by norm_num) (pow_nonneg hc0 3)
      have h := mul_le_mul_of_nonneg_left (neg_le_abs A3) hd0
      have e : -((1 / 3) * ((a + lam₁) / L) ^ 3 * A3)
          = ((1 / 3) * ((a + lam₁) / L) ^ 3) * (-A3) := by ring
      rw [e]; exact h
    have h4 : ((a + lam₁) / L) * |A1| ≤ ((a + lam₁) / L) * (M0 + 2 * S1) :=
      mul_le_mul_of_nonneg_left hA1 hc0
    have h5 : ((a + lam₁) / L) ^ 2 * |A2| ≤ ((a + lam₁) / L) ^ 2 * (M0 + 4 * S2) :=
      mul_le_mul_of_nonneg_left hA2 (pow_nonneg hc0 2)
    have h6 : (1 / 3) * ((a + lam₁) / L) ^ 3 * |A3|
        ≤ (1 / 3) * ((a + lam₁) / L) ^ 3 * (M0 + 16 * S3) :=
      mul_le_mul_of_nonneg_left hA3 (mul_nonneg (by norm_num) (pow_nonneg hc0 3))
    have hkey : ((a + lam₁) / L) * (M0 + 2 * S1) + ((a + lam₁) / L) ^ 2 * (M0 + 4 * S2)
        + (1 / 3) * ((a + lam₁) / L) ^ 3 * (M0 + 16 * S3) ≤ (a + lam₁) * e :=
      Work.ZeroFreeTables.Table4.final_arith (L := L) (α := a + lam₁) (Amax := a + M)
        (M0 := M0) (C := C0) (ε := e) (S1 := S1) (S2 := S2) (S3 := S3)
        hL1 (by linarith only [ha, hlam0]) (by linarith only [hlamM]) hS1b hS2b hS3b (le_of_lt hM0pos) (le_of_lt hC0pos)
        (hL0arith L hL0le)
    linarith only [h1, h2, h3, h4, h5, h6, hkey, this]
  rw [hsigA]
  linarith only [hfin, this]

end Work.ZeroFreeTables.HB95h2
