import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.zetaLogDeriv_pole_split
import Submission.Work.ZeroFreeTables.P9.zetaDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs
import Submission.Work.ZeroFreeTables.Table4.FarNear
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.ZeroFreeTables.P9.tsum_inv_add_two_shift
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le
import Submission.Work.ZeroFreeTables.Table4.zetaSmoothBound
import Submission.Work.ZeroFreeTables.Table4.eulerFactorBound
import Submission.Work.ZeroFreeTables.Table4.logDerivPrincipalDecomp
import Submission.Work.ZeroFreeTables.Table4.principalArith

open scoped BigOperators
open Finset

namespace Work.ZeroFreeTables.Table4

lemma final_arith {L α Amax M0 C ε S1 S2 S3 : ℝ}
    (hL : 1 ≤ L) (hα : 0 < α) (hαA : α ≤ Amax)
    (hS1 : S1 ≤ C * (Real.log L + 2) ^ 2)
    (hS2 : S2 ≤ C * (Real.log L + 2) ^ 3)
    (hS3 : S3 ≤ C * (Real.log L + 2) ^ 4)
    (hM0 : 0 ≤ M0) (hC : 0 ≤ C)
    (ht : M0 * (1 + Amax / L + Amax ^ 2 / (3 * L ^ 2)) / L + 2 * C * (Real.log L + 2) ^ 2 / L
        + 4 * Amax * C * (Real.log L + 2) ^ 3 / L ^ 2
        + (16 / 3) * Amax ^ 2 * C * (Real.log L + 2) ^ 4 / L ^ 3 ≤ ε) :
    (α / L) * (M0 + 2 * S1) + (α / L) ^ 2 * (M0 + 4 * S2)
      + (1 / 3) * (α / L) ^ 3 * (M0 + 16 * S3) ≤ α * ε := by
  set A2 : ℝ := (Real.log L + 2) ^ 2 with hA2
  set A3 : ℝ := (Real.log L + 2) ^ 3 with hA3
  set A4 : ℝ := (Real.log L + 2) ^ 4 with hA4
  have hLpos : 0 < L := by linarith
  have hαL0 : 0 ≤ α / L := le_of_lt (div_pos hα hLpos)
  have hbase : 0 ≤ Real.log L + 2 := by have := Real.log_nonneg hL; linarith
  have hA2n : 0 ≤ A2 := by rw [hA2]; positivity
  have hA3n : 0 ≤ A3 := by rw [hA3]; positivity
  have hA4n : 0 ≤ A4 := by rw [hA4]; positivity
  have e1 : (α / L) * (M0 + 2 * S1) ≤ (α / L) * (M0 + 2 * (C * A2)) := by
    apply mul_le_mul_of_nonneg_left _ hαL0
    linarith [hS1]
  have e2 : (α / L) ^ 2 * (M0 + 4 * S2) ≤ (α / L) ^ 2 * (M0 + 4 * (C * A3)) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hαL0 2)
    linarith [hS2]
  have e3 : (1 / 3) * (α / L) ^ 3 * (M0 + 16 * S3) ≤ (1 / 3) * (α / L) ^ 3 * (M0 + 16 * (C * A4)) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (pow_nonneg hαL0 3))
    linarith [hS3]
  have hle1 : (α / L) * (M0 + 2 * (C * A2)) ≤ α * (M0 / L + 2 * (C * A2) / L) :=
    le_of_eq (by ring)
  have hle2 : (α / L) ^ 2 * (M0 + 4 * (C * A3))
      ≤ α * (Amax * M0 / L ^ 2 + 4 * Amax * (C * A3) / L ^ 2) := by
    have he : (α / L) ^ 2 * (M0 + 4 * (C * A3)) = α * ((α / L ^ 2) * (M0 + 4 * (C * A3))) := by ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hα)
    have h3 : α / L ^ 2 ≤ Amax / L ^ 2 :=
      div_le_div_of_nonneg_right hαA (by positivity)
    have h4 : 0 ≤ M0 + 4 * (C * A3) := by
      have : 0 ≤ C * A3 := mul_nonneg hC hA3n
      linarith
    calc (α / L ^ 2) * (M0 + 4 * (C * A3)) ≤ (Amax / L ^ 2) * (M0 + 4 * (C * A3)) :=
          mul_le_mul_of_nonneg_right h3 h4
      _ = Amax * M0 / L ^ 2 + 4 * Amax * (C * A3) / L ^ 2 := by ring
  have hle3 : (1 / 3) * (α / L) ^ 3 * (M0 + 16 * (C * A4))
      ≤ α * ((1 / 3) * Amax ^ 2 * M0 / L ^ 3 + (16 / 3) * Amax ^ 2 * (C * A4) / L ^ 3) := by
    have he : (1 / 3) * (α / L) ^ 3 * (M0 + 16 * (C * A4))
        = α * ((1 / 3) * (α ^ 2 / L ^ 3) * (M0 + 16 * (C * A4))) := by ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hα)
    have h3 : α ^ 2 / L ^ 3 ≤ Amax ^ 2 / L ^ 3 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (le_of_lt hα) hαA 2) (by positivity)
    have h4 : 0 ≤ M0 + 16 * (C * A4) := by
      have : 0 ≤ C * A4 := mul_nonneg hC hA4n
      linarith
    calc (1 / 3) * (α ^ 2 / L ^ 3) * (M0 + 16 * (C * A4))
        ≤ (1 / 3) * (Amax ^ 2 / L ^ 3) * (M0 + 16 * (C * A4)) := by
          apply mul_le_mul_of_nonneg_right _ h4
          apply mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = (1 / 3) * Amax ^ 2 * M0 / L ^ 3 + (16 / 3) * Amax ^ 2 * (C * A4) / L ^ 3 := by ring
  have e1' : α * (M0 / L + 2 * (C * A2) / L) = α * (M0 / L) + α * (2 * (C * A2) / L) := by ring
  have e2' : α * (Amax * M0 / L ^ 2 + 4 * Amax * (C * A3) / L ^ 2)
      = α * (Amax * M0 / L ^ 2) + α * (4 * Amax * (C * A3) / L ^ 2) := by ring
  have e3' : α * ((1 / 3) * Amax ^ 2 * M0 / L ^ 3 + (16 / 3) * Amax ^ 2 * (C * A4) / L ^ 3)
      = α * ((1 / 3) * Amax ^ 2 * M0 / L ^ 3) + α * ((16 / 3) * Amax ^ 2 * (C * A4) / L ^ 3) := by ring
  have hcomb2 : α * (M0 / L) + α * (2 * (C * A2) / L) + α * (Amax * M0 / L ^ 2)
      + α * (4 * Amax * (C * A3) / L ^ 2) + α * ((1 / 3) * Amax ^ 2 * M0 / L ^ 3)
      + α * ((16 / 3) * Amax ^ 2 * (C * A4) / L ^ 3)
      = α * (M0 * (1 + Amax / L + Amax ^ 2 / (3 * L ^ 2)) / L + 2 * C * A2 / L
          + 4 * Amax * C * A3 / L ^ 2 + (16 / 3) * Amax ^ 2 * C * A4 / L ^ 3) := by ring
  have hW : M0 * (1 + Amax / L + Amax ^ 2 / (3 * L ^ 2)) / L + 2 * C * A2 / L
      + 4 * Amax * C * A3 / L ^ 2 + (16 / 3) * Amax ^ 2 * C * A4 / L ^ 3 ≤ ε := ht
  calc (α / L) * (M0 + 2 * S1) + (α / L) ^ 2 * (M0 + 4 * S2) + (1 / 3) * (α / L) ^ 3 * (M0 + 16 * S3)
      ≤ (α / L) * (M0 + 2 * (C * A2)) + (α / L) ^ 2 * (M0 + 4 * (C * A3))
          + (1 / 3) * (α / L) ^ 3 * (M0 + 16 * (C * A4)) := by linarith [e1, e2, e3]
    _ ≤ α * (M0 / L) + α * (2 * (C * A2) / L) + α * (Amax * M0 / L ^ 2)
          + α * (4 * Amax * (C * A3) / L ^ 2) + α * ((1 / 3) * Amax ^ 2 * M0 / L ^ 3)
          + α * ((16 / 3) * Amax ^ 2 * (C * A4) / L ^ 3) := by
        linarith [hle1, hle2, hle3, e1', e2', e3']
    _ = α * (M0 * (1 + Amax / L + Amax ^ 2 / (3 * L ^ 2)) / L + 2 * C * A2 / L
          + 4 * Amax * C * A3 / L ^ 2 + (16 / 3) * Amax ^ 2 * C * A4 / L ^ 3) := hcomb2
    _ ≤ α * ε := mul_le_mul_of_nonneg_left hW (le_of_lt hα)



set_option maxHeartbeats 8000000 in
theorem principal_bound {a M ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ {q : ℕ} [NeZero q], Real.log (q : ℝ) = L →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 4 →
      ∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ ≤ M →
        Work.ZeroFreeTables.SigmaP3L q L 1 s a lam₁ ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + (a + lam₁) * ε := by
  rcases lt_or_ge M 0 with hMneg | hMge
  · refine ⟨0, ?_⟩
    intro L _ q _ _ s _ _ lam₁ h0 hle
    exact absurd (by linarith : lam₁ < 0) (not_lt.mpr h0)
  obtain ⟨M0, hM0pos, hzB⟩ := zetaSmoothBound
  obtain ⟨C1, hC1pos, hC1⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨C2, hC2pos, hC2⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨C3, hC3pos, hC3⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  set C : ℝ := max C1 (max C2 C3) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le hC1pos (le_max_left _ _)
  have hC1le : C1 ≤ C := le_max_left _ _
  have hC2le : C2 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC3le : C3 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨L0, hL01, hL0⟩ := principalArith M0 C (a + M) ε hM0pos hCpos (by linarith) hε
  refine ⟨max (max L0 2) (3 * a), ?_⟩
  intro L hL q hqne hqL s hsre him lam₁ hlam0 hlamM
  have hL0le : L0 ≤ L := le_trans (le_trans (le_max_left L0 2) (le_max_left _ _)) hL
  have hL2 : 2 ≤ L := le_trans (le_trans (le_max_right L0 2) (le_max_left _ _)) hL
  have hL3a : 3 * a ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := by linarith
  have hsre1 : 1 < s.re := by
    rw [hsre]; have : 0 < a / L := div_pos ha hLpos; linarith
  have hsre4 : s.re ≤ 4 := by
    rw [hsre]
    have h1 : a / L ≤ 1 / 3 := by rw [div_le_iff₀ hLpos]; linarith
    linarith
  have him5 : |s.im| ≤ 5 := by linarith
  have hq3 : 3 ≤ q := by
    by_contra h
    have hqle : q ≤ 2 := by omega
    have h1 : Real.log (q : ℝ) ≤ Real.log 2 := Real.log_le_log (show (0:ℝ) < (q:ℝ) by exact_mod_cast (NeZero.pos q)) (by exact_mod_cast hqle)
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    rw [hqL] at h1
    linarith
  obtain ⟨hz0, hz1, hz2⟩ := hzB s hsre1 hsre4 him5
  obtain ⟨hE0, hE1, hE2⟩ := eulerFactorBound q (le_of_lt hsre1)
  set Rf : ℂ → ℂ := fun z => ∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1) with hRfdef
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
  have hES1 : ‖Rf s‖ ≤ 2 * S1 := by
    rw [← hE0sum, hRfdef]
    simpa using hE0
  have hES2 : ‖iteratedDeriv 1 Rf s‖ ≤ 4 * S2 := by
    rw [← hE1sum]
    simpa using hE1
  have hES3 : ‖iteratedDeriv 2 Rf s‖ ≤ 16 * S3 := by
    rw [← hE2sum]
    exact hE2
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hC1b : S1 ≤ C1 * (Real.log L) ^ 2 := by
    have h := hC1 q hq3
    have e : (Real.log (Real.log (q : ℝ))) ^ (1 + 1) = (Real.log L) ^ 2 := by simp [hqL]
    rw [e] at h
    rw [hS1def]
    simpa [pow_one] using h
  have hS1b : S1 ≤ C * (Real.log L + 2) ^ 2 := by
    refine le_trans hC1b ?_
    have hs : (Real.log L) ^ 2 ≤ (Real.log L + 2) ^ 2 := by nlinarith
    have h1 : C1 * (Real.log L) ^ 2 ≤ C1 * (Real.log L + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (le_of_lt hC1pos)
    have h2 : C1 * (Real.log L + 2) ^ 2 ≤ C * (Real.log L + 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hC1le (by positivity)
    linarith
  have hC2b : S2 ≤ C2 * (Real.log L) ^ 3 := by
    have h := hC2 q hq3
    have e : (Real.log (Real.log (q : ℝ))) ^ (2 + 1) = (Real.log L) ^ 3 := by simp [hqL]
    rw [e] at h
    rw [hS2def]
    simpa using h
  have hS2b : S2 ≤ C * (Real.log L + 2) ^ 3 := by
    refine le_trans hC2b ?_
    have hs : (Real.log L) ^ 3 ≤ (Real.log L + 2) ^ 3 := by nlinarith
    have h1 : C2 * (Real.log L) ^ 3 ≤ C2 * (Real.log L + 2) ^ 3 :=
      mul_le_mul_of_nonneg_left hs (le_of_lt hC2pos)
    have h2 : C2 * (Real.log L + 2) ^ 3 ≤ C * (Real.log L + 2) ^ 3 :=
      mul_le_mul_of_nonneg_right hC2le (by positivity)
    linarith
  have hC3b : S3 ≤ C3 * (Real.log L) ^ 4 := by
    have h := hC3 q hq3
    have e : (Real.log (Real.log (q : ℝ))) ^ (3 + 1) = (Real.log L) ^ 4 := by simp [hqL]
    rw [e] at h
    rw [hS3def]
    simpa using h
  have hS3b : S3 ≤ C * (Real.log L + 2) ^ 4 := by
    refine le_trans hC3b ?_
    have hs : (Real.log L) ^ 4 ≤ (Real.log L + 2) ^ 4 := by nlinarith
    have h1 : C3 * (Real.log L) ^ 4 ≤ C3 * (Real.log L + 2) ^ 4 :=
      mul_le_mul_of_nonneg_left hs (le_of_lt hC3pos)
    have h2 : C3 * (Real.log L + 2) ^ 4 ≤ C * (Real.log L + 2) ^ 4 :=
      mul_le_mul_of_nonneg_right hC3le (by positivity)
    linarith
  have hlog0 : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
      = logDeriv riemannZeta s + Rf s := by
    have hd0 := logDerivPrincipalDecomp q 0 (by norm_num) hsre1
    rw [← hRfdef] at hd0
    simpa [iteratedDeriv_zero] using hd0
  have hlog1 : iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
      = iteratedDeriv 1 (logDeriv riemannZeta) s + iteratedDeriv 1 Rf s := by
    have hd1 := logDerivPrincipalDecomp q 1 (by norm_num) hsre1
    rw [← hRfdef] at hd1
    exact hd1
  have hlog2 : iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
      = iteratedDeriv 2 (logDeriv riemannZeta) s + iteratedDeriv 2 Rf s := by
    have hd2 := logDerivPrincipalDecomp q 2 (by norm_num) hsre1
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
      linarith [hES1]
    calc |(logDeriv riemannZeta s + 1 / (s - 1)).re + (Rf s).re|
        ≤ |(logDeriv riemannZeta s + 1 / (s - 1)).re| + |(Rf s).re| := abs_add_le _ _
      _ ≤ M0 + 2 * S1 := by linarith [hz0, hr]
  have hA2 : |A2| ≤ M0 + 4 * S2 := by
    have h1 : A2 = (iteratedDeriv 1 (logDeriv riemannZeta) s - (1 / (s - 1)) ^ 2).re
        + (iteratedDeriv 1 Rf s).re := by
      rw [hA2def, hlog1]
      simp only [Complex.add_re, Complex.sub_re]
      ring
    rw [h1]
    have hr : |(iteratedDeriv 1 Rf s).re| ≤ 4 * S2 := by
      have := Complex.abs_re_le_norm (iteratedDeriv 1 Rf s)
      linarith [hES2]
    calc |(iteratedDeriv 1 (logDeriv riemannZeta) s - (1 / (s - 1)) ^ 2).re + (iteratedDeriv 1 Rf s).re|
        ≤ |(iteratedDeriv 1 (logDeriv riemannZeta) s - (1 / (s - 1)) ^ 2).re| + |(iteratedDeriv 1 Rf s).re| := abs_add_le _ _
      _ ≤ M0 + 4 * S2 := by linarith [hz1', hr]
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
      linarith [hES3]
    calc |(iteratedDeriv 2 (logDeriv riemannZeta) s + 2 * (1 / (s - 1)) ^ 3).re + (iteratedDeriv 2 Rf s).re|
        ≤ |(iteratedDeriv 2 (logDeriv riemannZeta) s + 2 * (1 / (s - 1)) ^ 3).re| + |(iteratedDeriv 2 Rf s).re| := abs_add_le _ _
      _ ≤ M0 + 16 * S3 := by linarith [hz2', hr]
  have hsig := Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs (1 : DirichletCharacter ℂ q) hsre1 a lam₁ L
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
      - (1 / 3) * ((a + lam₁) / L) ^ 3 * A3 ≤ (a + lam₁) * ε := by
    have hc0 : 0 ≤ (a + lam₁) / L := div_nonneg (by linarith) (le_of_lt hLpos)
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
      have e : -((1 / 3) * ((a + lam₁) / L) ^ 3 * A3) = ((1 / 3) * ((a + lam₁) / L) ^ 3) * (-A3) := by ring
      rw [e]; exact h
    have h4 : ((a + lam₁) / L) * |A1| ≤ ((a + lam₁) / L) * (M0 + 2 * S1) :=
      mul_le_mul_of_nonneg_left hA1 hc0
    have h5 : ((a + lam₁) / L) ^ 2 * |A2| ≤ ((a + lam₁) / L) ^ 2 * (M0 + 4 * S2) :=
      mul_le_mul_of_nonneg_left hA2 (pow_nonneg hc0 2)
    have h6 : (1 / 3) * ((a + lam₁) / L) ^ 3 * |A3| ≤ (1 / 3) * ((a + lam₁) / L) ^ 3 * (M0 + 16 * S3) :=
      mul_le_mul_of_nonneg_left hA3 (mul_nonneg (by norm_num) (pow_nonneg hc0 3))
    have hkey : ((a + lam₁) / L) * (M0 + 2 * S1) + ((a + lam₁) / L) ^ 2 * (M0 + 4 * S2)
        + (1 / 3) * ((a + lam₁) / L) ^ 3 * (M0 + 16 * S3) ≤ (a + lam₁) * ε :=
      final_arith (α := a + lam₁) (Amax := a + M) (by linarith : (1:ℝ) ≤ L) (by linarith) (by linarith) hS1b hS2b hS3b
        (le_of_lt hM0pos) (le_of_lt hCpos) (hL0 L hL0le)
    linarith [h1, h2, h3, h4, h5, h6, hkey]
  rw [hsigA]
  linarith [hfin]


end Work.ZeroFreeTables.Table4
