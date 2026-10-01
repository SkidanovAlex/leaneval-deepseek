import Mathlib
import Submission.Work.ZeroFreeTables.P9.pointEngine_prim

open DirichletCharacter Complex
open scoped BigOperators
open Work.ZeroFreeTables.P9

namespace Work.ZeroFreeTables.OffAxis

/-- Summability of the parity ("trivial zero") series `∑_n (s + par + 2n)^{-(k+1)}`. -/
private lemma summable_parity (par : ℕ) {s : ℂ} (hs : 1 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hs' : 1 < (s + (par : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (par : ℝ) := Nat.cast_nonneg par
    linarith
  have h := (tsum_inv_add_two_shift k hk (s := s + (par : ℂ)) hs').1
  refine h.congr (fun n => ?_)
  have hh : (s + (par : ℂ)) + ((2 * n : ℕ) : ℂ) = s + ((par + 2 * n : ℕ) : ℂ) := by
    push_cast; ring
  rw [hh]

theorem pointEngine_prim_gen {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {a lam₁ δ c L Ct : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L) (haδL : 2 * a ≤ δ * L)
    {s : ℂ} (hsre : s.re = 1 + a / L)
    (hlog : (-logDeriv (DirichletCharacter.LFunction χ) s).re
        + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L)
    (par : ℕ) (hpar0 : χ.Even → par = 0) (hpar1 : χ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct) :
    Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      ≤ -(Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ) + (a + lam₁) * c
        + ((a + lam₁) ^ 2 / L ^ 2)
            * ((1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3)
            * ((2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct) := by
  -- ## basic positivity / size facts
  have hLpos : 0 < L := by linarith
  have hs_gt : 1 < s.re := by
    rw [hsre]
    have : 0 < a / L := div_pos ha hLpos
    linarith
  have hsδ : s.re ≤ 1 + δ / 2 := by
    rw [hsre]
    have h1 : a / L ≤ δ / 2 := by
      rw [div_le_iff₀ hLpos]
      nlinarith [haδL]
    linarith
  have haL_nonneg : 0 ≤ (a + lam₁) / L := div_nonneg (by linarith) (le_of_lt hLpos)
  -- ## the differentiated explicit formula, k = 1 and k = 2
  obtain ⟨hsum2, hform2⟩ := lDiffExplicit_gen χ hχ hprim 1 (by norm_num) par hpar0 hpar1 hs_gt
  obtain ⟨hsum3, hform3⟩ := lDiffExplicit_gen χ hχ hprim 2 (by norm_num) par hpar0 hpar1 hs_gt
  have hF2 : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2)
      + (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)
      = - iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s := by
    simpa using hform2
  have hF3 : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)
      + (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)
      = ((1 / 2 : ℝ) : ℂ) * iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s := by
    simpa using hform3
  have hBs2 : Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2) :=
    summable_parity par hs_gt 1 (by norm_num)
  have hBs3 : Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3) :=
    summable_parity par hs_gt 2 (by norm_num)
  -- ## abbreviations
  set A2 : ℂ := ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2 with hA2def
  set A3 : ℂ := ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3 with hA3def
  set B2 : ℂ := ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2 with hB2def
  set B3 : ℂ := ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3 with hB3def
  set M0 : ℝ := (logDeriv (DirichletCharacter.LFunction χ) s).re with hM0def
  set M1 : ℝ := (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s).re with hM1def
  set M2 : ℝ := (iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s).re with hM2def
  set b2 : ℝ := ∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re with hb2def
  set b3 : ℝ := ∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re with hb3def
  set Q : ℝ := ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u
      * ((1 / (s - u)) ^ 2).re with hQdef
  set C3 : ℝ := ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u
      * ((1 / (s - u)) ^ 3).re with hC3def
  set J : ℝ := Work.ZeroFreeTables.P9.invSqSum N χ s with hJdef
  set NI : ℝ := Work.ZeroFreeTables.P9.nearInvSum N χ s δ with hNIdef
  set P3S : ℝ := Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ with hP3Sdef
  -- ## real parts of the two parity sums, from summability
  have hB2re : B2.re = b2 := by rw [hB2def, hb2def]; exact Complex.re_tsum hBs2
  have hB3re : B3.re = b3 := by rw [hB3def, hb3def]; exact Complex.re_tsum hBs3
  -- ## M1, M2 in terms of the zero sums and the parity sums
  have hM1rel : M1 = - A2.re - b2 := by
    rw [hM1def]
    have h := congrArg Complex.re hF2
    rw [Complex.add_re, Complex.neg_re, hB2re] at h
    linarith
  have hM2rel : M2 = 2 * A3.re + 2 * b3 := by
    rw [hM2def]
    have h := congrArg Complex.re hF3
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hB3re] at h
    norm_num at h
    linarith
  -- ## the Sigma identity
  have hSig : Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      = - M0 * ((a + lam₁) / L) + ((a + lam₁) / L) ^ 2 * M1
        - (1 / 3) * ((a + lam₁) / L) ^ 3 * M2 := by
    have hB := Work.ZeroFreeTables.P9.prim.SigmaP3L_eq_moments χ hs_gt a lam₁ L
    have hA0 := Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re χ 0 hs_gt
    have hA1 := Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re χ 1 hs_gt
    have hA2 := Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re χ 2 hs_gt
    have hsub : ((a + lam₁) / L) * Work.ZeroFreeTables.vonMangoldtMoment χ s 0
          + ((a + lam₁) / L) ^ 2 * Work.ZeroFreeTables.vonMangoldtMoment χ s 1
          + (1 / 3) * ((a + lam₁) / L) ^ 3 * Work.ZeroFreeTables.vonMangoldtMoment χ s 2
        = - M0 * ((a + lam₁) / L) + ((a + lam₁) / L) ^ 2 * M1
          - (1 / 3) * ((a + lam₁) / L) ^ 3 * M2 := by
      have h0 : (logDeriv (DirichletCharacter.LFunction χ) s).re
          = - Work.ZeroFreeTables.vonMangoldtMoment χ s 0 := by simpa using hA0
      have h1 : (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s).re
          = Work.ZeroFreeTables.vonMangoldtMoment χ s 1 := by simpa using hA1
      have h2 : (iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s).re
          = - Work.ZeroFreeTables.vonMangoldtMoment χ s 2 := by rw [hA2]; ring_nf
      rw [hM0def, hM1def, hM2def, h0, h1, h2]
      ring
    rw [hB, hsub]
  -- ## the three term bounds
  have hquad : -A2.re ≤ -Q + (1 + 4 / δ ^ 2) * J := by
    have h := Work.ZeroFreeTables.P9.prim.quadNearFar χ hχ hprim hδ hδ1 hs_gt hsδ hsum2
    simpa only [← hA2def, ← hQdef, ← hJdef] using h
  have hcub : -A3.re ≤ -C3 + (2 / δ) * (1 + 4 / δ ^ 2) * J := by
    have h := Work.ZeroFreeTables.P9.prim.cubicNearFar χ hχ hprim hδ hδ1 hs_gt hsδ hsum3
    simpa only [← hA3def, ← hC3def, ← hJdef] using h
  have hb2ge : -Ct ≤ b2 := (abs_le.mp hS2).1
  have hb3ge : -Ct ≤ b3 := (abs_le.mp hS3).1
  have hstep1 : - M0 * ((a + lam₁) / L) ≤ (a + lam₁) * c - ((a + lam₁) / L) * NI := by
    have hlog' : -(logDeriv (DirichletCharacter.LFunction χ) s).re ≤ c * L - NI := by
      have h := hlog
      rw [Complex.neg_re] at h
      linarith
    have htL : ((a + lam₁) / L) * L = a + lam₁ := div_mul_cancel₀ _ hLpos.ne'
    have htLc : ((a + lam₁) / L) * (c * L) = (a + lam₁) * c := by
      have h : ((a + lam₁) / L) * (c * L) = (((a + lam₁) / L) * L) * c := by ring
      rw [h, htL]
    have hmul' : ((a + lam₁) / L) * (-(logDeriv (DirichletCharacter.LFunction χ) s).re)
        ≤ (a + lam₁) * c - ((a + lam₁) / L) * NI := by
      have hh := mul_le_mul_of_nonneg_left hlog' haL_nonneg
      rw [mul_sub, htLc] at hh
      exact hh
    rw [hM0def]
    linarith [hmul']
  have hstep2 : ((a + lam₁) / L) ^ 2 * M1
      ≤ ((a + lam₁) / L) ^ 2 * (-Q) + ((a + lam₁) / L) ^ 2 * (1 + 4 / δ ^ 2) * J
        + ((a + lam₁) / L) ^ 2 * Ct := by
    have ht2 : 0 ≤ ((a + lam₁) / L) ^ 2 := sq_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hquad ht2
    have h2 := mul_le_mul_of_nonneg_left hb2ge ht2
    rw [hM1rel]
    linarith [h1, h2]
  have hstep3 : - (1 / 3) * ((a + lam₁) / L) ^ 3 * M2
      ≤ (2 / 3) * ((a + lam₁) / L) ^ 3 * (-C3) + (2 / 3) * ((a + lam₁) / L) ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * J
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * Ct := by
    have ht3 : 0 ≤ (2 / 3) * ((a + lam₁) / L) ^ 3 :=
      mul_nonneg (by norm_num) (pow_nonneg haL_nonneg 3)
    have h1 := mul_le_mul_of_nonneg_left hcub ht3
    have h2 := mul_le_mul_of_nonneg_left hb3ge ht3
    rw [hM2rel]
    linarith [h1, h2]
  have hsplit : P3S = ((a + lam₁) / L) * NI + ((a + lam₁) / L) ^ 2 * Q
      + (2 / 3) * ((a + lam₁) / L) ^ 3 * C3 := by
    have h := Work.ZeroFreeTables.P9.prim.nearP3sum_split (a := a) (lam₁ := lam₁) (L := L) χ hχ hprim
      (s := s) (δ := δ) hδ hδ1 hs_gt hsδ hsum2 hsum3
    simpa only [← hP3Sdef, ← hNIdef, ← hQdef, ← hC3def] using h
  -- ## assembly
  calc Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      = - M0 * ((a + lam₁) / L) + ((a + lam₁) / L) ^ 2 * M1
          - (1 / 3) * ((a + lam₁) / L) ^ 3 * M2 := hSig
    _ ≤ ((a + lam₁) * c - ((a + lam₁) / L) * NI)
          + (((a + lam₁) / L) ^ 2 * (-Q) + ((a + lam₁) / L) ^ 2 * (1 + 4 / δ ^ 2) * J
              + ((a + lam₁) / L) ^ 2 * Ct)
          + ((2 / 3) * ((a + lam₁) / L) ^ 3 * (-C3)
              + (2 / 3) * ((a + lam₁) / L) ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * J
              + (2 / 3) * ((a + lam₁) / L) ^ 3 * Ct) := by
        linarith [hstep1, hstep2, hstep3]
    _ = - P3S + (a + lam₁) * c
          + ((a + lam₁) / L) ^ 2 * ((1 + 4 / δ ^ 2) * J + Ct)
          + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct) := by
        rw [hsplit]; ring
    _ = - P3S + (a + lam₁) * c
          + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * J + Ct)
          + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct) := by
        rw [div_pow, div_pow]

end Work.ZeroFreeTables.OffAxis
