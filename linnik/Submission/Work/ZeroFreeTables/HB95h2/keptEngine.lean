import Mathlib
import Submission.Work.ZeroFreeTables.Table4.Engine8
import Submission.Work.ZeroFreeTables.Table4.FarNear
import Submission.Work.ZeroFreeTables.P9.lDiffExplicit_gen

namespace Work.ZeroFreeTables.HB95h2

private lemma summable_parity_series (par : ℕ) {s : ℂ} (hs : 1 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hs' : 1 < (s + (par : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (par : ℝ) := Nat.cast_nonneg par
    linarith
  have h := (Work.ZeroFreeTables.P9.tsum_inv_add_two_shift k hk (s := s + (par : ℂ)) hs').1
  refine h.congr (fun n => ?_)
  have hh : (s + (par : ℂ)) + ((2 * n : ℕ) : ℂ) = s + ((par + 2 * n : ℕ) : ℂ) := by
    push_cast; ring
  rw [hh]

set_option maxHeartbeats 4000000 in
theorem keptEngine {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {a lam₁ δ c L Ct : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hLpos : 0 < L) {s : ℂ} (hs : 1 < s.re)
    (hsδ : s.re ≤ 1 + δ / 2)
    (hlog : (-logDeriv (DirichletCharacter.LFunction χ) s).re
        + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L)
    (par : ℕ) (hpar0 : χ.Even → par = 0) (hpar1 : χ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    {S : Finset ℂ}
    (h1 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
        * Work.ZeroFreeTables.Table4.keptInd S s δ u * ((1 / (s - u)).re)))
    (h2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
        * Work.ZeroFreeTables.Table4.keptInd S s δ u * ((1 / (s - u)) ^ 2).re))
    (h3 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
        * Work.ZeroFreeTables.Table4.keptInd S s δ u * ((1 / (s - u)) ^ 3).re))
    (hsum2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2))
    (hsum3 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)) :
    Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      ≤ - (Work.ZeroFreeTables.Table4.keptP3Sum N L χ s a lam₁ δ S)
        + (a + lam₁) * c
        + ((a + lam₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
            * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re)))
        + ((a + lam₁) ^ 2 / L ^ 2)
            * ((1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3)
            * ((2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct) := by
  classical
  have hdel1 : δ ≤ 1 := le_of_lt hδ1
  have hann : 0 ≤ (a + lam₁) / L := div_nonneg (by linarith) hLpos.le
  -- ## the two differentiated explicit formulae (k = 1 and k = 2)
  obtain ⟨_, hform2⟩ :=
    Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 1 (by norm_num) par hpar0 hpar1 hs
  obtain ⟨_, hform3⟩ :=
    Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 2 (by norm_num) par hpar0 hpar1 hs
  have hF2 : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2)
      + (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)
      = - iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s := by
    simpa using hform2
  have hF3 : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)
      + (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)
      = ((1 / 2 : ℝ) : ℂ) * iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s := by
    simpa using hform3
  have hBs2 : Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2) :=
    summable_parity_series par hs 1 (by norm_num)
  have hBs3 : Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3) :=
    summable_parity_series par hs 2 (by norm_num)
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
  -- ## real parts of the parity sums
  have hB2re : B2.re = b2 := by
    rw [hB2def, hb2def]
    exact Complex.re_tsum hBs2
  have hB3re : B3.re = b3 := by
    rw [hB3def, hb3def]
    exact Complex.re_tsum hBs3
  -- ## the two log-derivative moments in terms of the zero sums and the parity sums
  have hM1rel : M1 = -A2.re - b2 := by
    rw [hM1def]
    have h := congrArg Complex.re hF2
    rw [Complex.add_re, Complex.neg_re, hB2re] at h
    linarith
  have hM2rel : M2 = 2 * A3.re + 2 * b3 := by
    rw [hM2def]
    have h := congrArg Complex.re hF3
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hB3re] at h
    norm_num at h
    linarith
  -- ## the `SigmaP3L` identity (HB §8.2)
  have hSig : Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      = -((a + lam₁) / L) * M0 + ((a + lam₁) / L) ^ 2 * M1
        - (1 / 3) * ((a + lam₁) / L) ^ 3 * M2 := by
    have h := Work.ZeroFreeTables.Table4.SigmaP3L_eq_derivs χ hs a lam₁ L
    simpa only [← hM0def, ← hM1def, ← hM2def] using h
  -- ## the near/far bounds for the kept square and cube sums
  have hquad : -A2.re ≤ - Work.ZeroFreeTables.Table4.keptSqSum N χ s δ S
      + (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s := by
    have h := Work.ZeroFreeTables.Table4.quadNearFar_kept χ hχ hprim hδ hδ1 hs hsδ hsum2 S
    rw [← hA2def] at h
    simp only [Work.ZeroFreeTables.Table4.keptSqSum, Work.ZeroFreeTables.P9.invSqSum] at h ⊢
    exact h
  have hcub : -A3.re ≤ - Work.ZeroFreeTables.Table4.keptCubSum N χ s δ S
      + (2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s := by
    have h := Work.ZeroFreeTables.Table4.cubicNearFar_kept χ hχ hprim hδ hδ1 hs hsδ hsum3 S
    rw [← hA3def] at h
    simp only [Work.ZeroFreeTables.Table4.keptCubSum, Work.ZeroFreeTables.P9.invSqSum] at h ⊢
    exact h
  -- ## the parity bounds
  have hb2ge : -Ct ≤ b2 := by
    have h : |b2| ≤ Ct := by simpa only [hb2def] using hS2
    exact (abs_le.mp h).1
  have hb3ge : -Ct ≤ b3 := by
    have h : |b3| ≤ Ct := by simpa only [hb3def] using hS3
    exact (abs_le.mp h).1
  -- ## the `k = 1` step, in its kept form
  have hk1 : -M0 * ((a + lam₁) / L)
      ≤ (a + lam₁) * c - ((a + lam₁) / L) * Work.ZeroFreeTables.Table4.keptInvSum N χ s δ S
        + ((a + lam₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
            * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))) := by
    have h := Work.ZeroFreeTables.Table4.k1_link χ hχ hprim ha hlam₁ hLpos hδ hdel1 hlog h1
    simpa only [← hM0def] using h
  -- ## the three term bounds
  have ht2 : 0 ≤ ((a + lam₁) / L) ^ 2 := sq_nonneg _
  have ht3 : 0 ≤ (2 / 3) * ((a + lam₁) / L) ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg hann 3)
  have hstep2 : ((a + lam₁) / L) ^ 2 * M1
      ≤ ((a + lam₁) / L) ^ 2 * (-(Work.ZeroFreeTables.Table4.keptSqSum N χ s δ S))
        + ((a + lam₁) / L) ^ 2 * ((1 + 4 / δ ^ 2)
            * Work.ZeroFreeTables.P9.invSqSum N χ s)
        + ((a + lam₁) / L) ^ 2 * Ct := by
    have h1a := mul_le_mul_of_nonneg_left hquad ht2
    have h2a := mul_le_mul_of_nonneg_left hb2ge ht2
    rw [hM1rel]
    linarith [h1a, h2a]
  have hstep3 : - (1 / 3) * ((a + lam₁) / L) ^ 3 * M2
      ≤ (2 / 3) * ((a + lam₁) / L) ^ 3 * (-(Work.ZeroFreeTables.Table4.keptCubSum N χ s δ S))
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((2 / δ) * (1 + 4 / δ ^ 2)
            * Work.ZeroFreeTables.P9.invSqSum N χ s)
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * Ct := by
    have h1a := mul_le_mul_of_nonneg_left hcub ht3
    have h2a := mul_le_mul_of_nonneg_left hb3ge ht3
    rw [hM2rel]
    linarith [h1a, h2a]
  -- ## the kept `P₃` split
  have hfold : Work.ZeroFreeTables.Table4.keptP3Sum N L χ s a lam₁ δ S
      = ((a + lam₁) / L) * Work.ZeroFreeTables.Table4.keptInvSum N χ s δ S
        + ((a + lam₁) / L) ^ 2 * Work.ZeroFreeTables.Table4.keptSqSum N χ s δ S
        + (2 / 3) * ((a + lam₁) / L) ^ 3
            * Work.ZeroFreeTables.Table4.keptCubSum N χ s δ S :=
    Work.ZeroFreeTables.Table4.keptP3Sum_split χ h1 h2 h3
  -- ## assembly
  calc Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      = -((a + lam₁) / L) * M0 + ((a + lam₁) / L) ^ 2 * M1
          - (1 / 3) * ((a + lam₁) / L) ^ 3 * M2 := hSig
    _ ≤ ((a + lam₁) * c - ((a + lam₁) / L) * Work.ZeroFreeTables.Table4.keptInvSum N χ s δ S
            + ((a + lam₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
                * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))))
          + (((a + lam₁) / L) ^ 2 * (-(Work.ZeroFreeTables.Table4.keptSqSum N χ s δ S))
              + ((a + lam₁) / L) ^ 2 * ((1 + 4 / δ ^ 2)
                  * Work.ZeroFreeTables.P9.invSqSum N χ s)
              + ((a + lam₁) / L) ^ 2 * Ct)
          + ((2 / 3) * ((a + lam₁) / L) ^ 3
                * (-(Work.ZeroFreeTables.Table4.keptCubSum N χ s δ S))
              + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((2 / δ) * (1 + 4 / δ ^ 2)
                  * Work.ZeroFreeTables.P9.invSqSum N χ s)
              + (2 / 3) * ((a + lam₁) / L) ^ 3 * Ct) := by
        linarith [hk1, hstep2, hstep3]
    _ = - Work.ZeroFreeTables.Table4.keptP3Sum N L χ s a lam₁ δ S
          + (a + lam₁) * c
          + ((a + lam₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
              * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re)))
          + ((a + lam₁) / L) ^ 2 * ((1 + 4 / δ ^ 2)
              * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
          + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((2 / δ) * (1 + 4 / δ ^ 2)
              * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct) := by
        rw [hfold]; ring
    _ = - Work.ZeroFreeTables.Table4.keptP3Sum N L χ s a lam₁ δ S
          + (a + lam₁) * c
          + ((a + lam₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
              * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re)))
          + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2)
              * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
          + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2)
              * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct) := by
        rw [div_pow, div_pow]



end Work.ZeroFreeTables.HB95h2
