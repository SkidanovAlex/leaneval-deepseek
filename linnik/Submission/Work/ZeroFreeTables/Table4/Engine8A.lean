/-
# ZeroFreeTables/Table4/Engine8A — the `P₃` engine of HB §8.2, axiom-free

This is the engine `pointEngine_prim` of `P9/pointEngine_prim.lean` with its four
`DevAux` axioms replaced by the proved lemmas of `P9/prim/*`:

* `quadNearFar`/`cubicNearFar`: the (`S = ∅`) instances of FarNear's `quadNearFar_kept`
  / `cubicNearFar_kept` — plain near/far split of the square/cube zero sums;
* `SigmaP3L_eq_moments`, `iteratedDeriv_logDeriv_re`: the moment identities of `P9/prim`;
* `nearP3sum_split`: the split of the near `P₃` sum (`P9/prim/nearP3sum_split`).

We also record the *extraction* lemmas: a single zero's `P₃`-term is dominated by the near
sum, up to the far cost `8α/(δL)` (`P3term_abs_le_of_far`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Table4.FarNear
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.lDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.SigmaP3LCoeffs
import Submission.Work.ZeroFreeTables.P9.tsum_inv_add_two_shift
import Submission.Work.ZeroFreeTables.P9.prim.SigmaP3L_eq_moments
import Submission.Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re
import Submission.Work.ZeroFreeTables.P9.prim.nearP3sum_split
import Submission.Work.ZeroFreeTables.P9.NearSummandDefs
import Submission.Work.ZeroFreeTables.P9.NearSummandLemmas
import Submission.Work.ZeroFreeTables.P3Pos

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.Table4

open Work.ZeroFreeTables

/-- `keptInd` at `S = ∅` is `nearInd`, in unfolded form. -/
lemma keptInd_empty_ite (s : ℂ) (δ : ℝ) (u : ℂ) :
    (if u ∈ (∅ : Finset ℂ) ∨ ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then (1 : ℝ) else 0)
      = Work.ZeroFreeTables.P9.nearInd s δ u := by
  rw [Work.ZeroFreeTables.P9.nearInd]
  simp

/-! ## The plain near/far splits -/

/-- The plain near/far split of the square zero sum, from the kept version with `S = ∅`. -/
theorem quadNearFar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 1 < s.re)
    (hsδ : s.re ≤ 1 + δ / 2)
    (hsum : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2)) :
    -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2).re
      ≤ -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) *
              Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 2).re)
        + (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s := by
  have h := quadNearFar_kept χ hχ hprim hδ hδ1 hs hsδ hsum (∅ : Finset ℂ)
  simp only [keptInd, keptInd_empty_ite, Work.ZeroFreeTables.P9.invSqSum] at h
  exact h

/-- The plain near/far split of the cube zero sum, from the kept version with `S = ∅`. -/
theorem cubicNearFar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 1 < s.re)
    (hsδ : s.re ≤ 1 + δ / 2)
    (hsum : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)) :
    -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3).re
      ≤ -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) *
              Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 3).re)
        + (2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s := by
  have h := cubicNearFar_kept χ hχ hprim hδ hδ1 hs hsδ hsum (∅ : Finset ℂ)
  simp only [keptInd, keptInd_empty_ite, Work.ZeroFreeTables.P9.invSqSum] at h
  exact h

/-! ## The engine -/

/-- Summability of the parity ("trivial zero") series `∑_n (s + par + 2n)^{-(k+1)}`. -/
private lemma summable_parity (par : ℕ) {s : ℂ} (hs : 1 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : ℕ => (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hs' : 1 < (s + (par : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (par : ℝ) := Nat.cast_nonneg par
    linarith only [hs]
  have h := (Work.ZeroFreeTables.P9.tsum_inv_add_two_shift k hk (s := s + (par : ℂ)) hs').1
  refine h.congr (fun n => ?_)
  have hh : (s + (par : ℂ)) + ((2 * n : ℕ) : ℂ) = s + ((par + 2 * n : ℕ) : ℂ) := by
    push_cast; ring
  rw [hh]

/-- **The `P₃` engine of HB §8.2** (proved, axiom-free).  For a primitive non-principal
character `χ`, at a point `s = 1 + a/L` with `|Im s| ≤ 10`, the log-derivative hypothesis of
HB Lemma 3.1 bounds `Σ(s,χ)` by the negated near-zero `P₃` sum plus the `k = 1` term `α·c`
and the quadratic/cubic far-zero errors. -/
theorem engine8 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {a lam₁ δ c L Ct : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L) (haδL : 2 * a ≤ δ * L)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 10)
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
  have hLpos : 0 < L := by linarith only [hδ, hδ1, hLt]
  have hs_gt : 1 < s.re := by
    rw [hsre]
    have : 0 < a / L := div_pos ha hLpos
    linarith only [this]
  have hsδ : s.re ≤ 1 + δ / 2 := by
    rw [hsre]
    have h1 : a / L ≤ δ / 2 := by
      rw [div_le_iff₀ hLpos]
      linarith only [haδL]
    linarith only [h1]
  have haL_nonneg : 0 ≤ (a + lam₁) / L := div_nonneg (by linarith only [ha, hlam₁]) (le_of_lt hLpos)
  obtain ⟨hsum2, hform2⟩ := P9.lDiffExplicit_gen χ hχ hprim 1 (by norm_num) par hpar0 hpar1 hs_gt
  obtain ⟨hsum3, hform3⟩ := P9.lDiffExplicit_gen χ hχ hprim 2 (by norm_num) par hpar0 hpar1 hs_gt
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
  set A2 : ℂ := ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2 with hA2def
  set A3 : ℂ := ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3 with hA3def
  set B2 : ℂ := ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2 with hB2def
  set B3 : ℂ := ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3 with hB3def
  set M0 : ℝ := (logDeriv (DirichletCharacter.LFunction χ) s).re with hM0def
  set M1 : ℝ := (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s).re with hM1def
  set M2 : ℝ := (iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s).re with hM2def
  set b2 : ℝ := ∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re with hb2def
  set b3 : ℝ := ∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re with hb3def
  set Q : ℝ := ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u
      * ((1 / (s - u)) ^ 2).re with hQdef
  set C3 : ℝ := ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u
      * ((1 / (s - u)) ^ 3).re with hC3def
  set J : ℝ := Work.ZeroFreeTables.P9.invSqSum N χ s with hJdef
  set NI : ℝ := Work.ZeroFreeTables.P9.nearInvSum N χ s δ with hNIdef
  set P3S : ℝ := Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ with hP3Sdef
  have hB2re : B2.re = b2 := by rw [hB2def, hb2def]; exact Complex.re_tsum hBs2
  have hB3re : B3.re = b3 := by rw [hB3def, hb3def]; exact Complex.re_tsum hBs3
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
  have hquad : -A2.re ≤ -Q + (1 + 4 / δ ^ 2) * J := by
    have h := quadNearFar χ hχ hprim hδ hδ1 hs_gt hsδ hsum2
    simpa only [← hA2def, ← hQdef, ← hJdef] using h
  have hcub : -A3.re ≤ -C3 + (2 / δ) * (1 + 4 / δ ^ 2) * J := by
    have h := cubicNearFar χ hχ hprim hδ hδ1 hs_gt hsδ hsum3
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
    linarith only [h1, h2]
  have hstep3 : - (1 / 3) * ((a + lam₁) / L) ^ 3 * M2
      ≤ (2 / 3) * ((a + lam₁) / L) ^ 3 * (-C3)
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * J
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * Ct := by
    have ht3 : 0 ≤ (2 / 3) * ((a + lam₁) / L) ^ 3 :=
      mul_nonneg (by norm_num) (pow_nonneg haL_nonneg 3)
    have h1 := mul_le_mul_of_nonneg_left hcub ht3
    have h2 := mul_le_mul_of_nonneg_left hb3ge ht3
    rw [hM2rel]
    linarith only [h1, h2]
  have hsplit : P3S = ((a + lam₁) / L) * NI + ((a + lam₁) / L) ^ 2 * Q
      + (2 / 3) * ((a + lam₁) / L) ^ 3 * C3 := by
    have h := Work.ZeroFreeTables.P9.prim.nearP3sum_split (a := a) (lam₁ := lam₁) (L := L)
      χ hχ hprim (s := s) (δ := δ) hδ hδ1 hs_gt hsδ hsum2 hsum3
    simpa only [← hP3Sdef, ← hNIdef, ← hQdef, ← hC3def] using h
  calc Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      = - M0 * ((a + lam₁) / L) + ((a + lam₁) / L) ^ 2 * M1
          - (1 / 3) * ((a + lam₁) / L) ^ 3 * M2 := hSig
    _ ≤ ((a + lam₁) * c - ((a + lam₁) / L) * NI)
          + (((a + lam₁) / L) ^ 2 * (-Q) + ((a + lam₁) / L) ^ 2 * (1 + 4 / δ ^ 2) * J
              + ((a + lam₁) / L) ^ 2 * Ct)
          + ((2 / 3) * ((a + lam₁) / L) ^ 3 * (-C3)
              + (2 / 3) * ((a + lam₁) / L) ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * J
              + (2 / 3) * ((a + lam₁) / L) ^ 3 * Ct) := by
        linarith only [hstep1, hstep2, hstep3]
    _ = - P3S + (a + lam₁) * c
          + ((a + lam₁) / L) ^ 2 * ((1 + 4 / δ ^ 2) * J + Ct)
          + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct) := by
        rw [hsplit]; ring
    _ = - P3S + (a + lam₁) * c
          + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * J + Ct)
          + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct) := by
        rw [div_pow, div_pow]

/-! ## The far cost of a single zero term, and the extraction of a single zero -/

/-- **The far cost.**  If `u` is outside the `δ`-window of the point `1 + i·Im s` (with
`s.re = 1 + a/L` and `2(a+λ₁) ≤ δL`), then the `P₃`-term of `u` is bounded by `8α/(δL)`. -/
theorem P3term_abs_le_of_far {a lam₁ L δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hδ : 0 < δ) (haδ : 2 * a ≤ δ * L) (hαδ : 2 * (a + lam₁) ≤ δ * L) {s u : ℂ}
    (hsre : s.re = 1 + a / L)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) :
    |(Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re| ≤ 8 * (a + lam₁) / (δ * L) := by
  have hα : 0 ≤ a + lam₁ := by linarith only [ha, hlam₁]
  have hδL : 0 < δ * L := mul_pos hδ hL
  have hsd : s - u = ((1 : ℂ) + (s.im : ℂ) * Complex.I - u) + (((s.re - 1 : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  have haL : (s.re - 1) * L = a := by
    rw [hsre, show (1 + a / L - 1) = a / L by ring, div_mul_cancel₀ _ (ne_of_gt hL)]
  have hdec : (s - u) * (L : ℂ)
      = ((1 : ℂ) + (s.im : ℂ) * Complex.I - u) * (L : ℂ) + ((a : ℝ) : ℂ) := by
    rw [hsd, add_mul]
    have h : (((s.re - 1 : ℝ)) : ℂ) * (L : ℂ) = ((a : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, haL]
    rw [h]
  have hnorm : δ * L - a ≤ ‖(s - u) * (L : ℂ)‖ := by
    rw [hdec]
    have h := norm_sub_le (((1 : ℂ) + (s.im : ℂ) * Complex.I - u) * (L : ℂ) + ((a : ℝ) : ℂ))
      (((a : ℝ)) : ℂ)
    rw [add_sub_cancel_right] at h
    have h2 : ‖((1 : ℂ) + (s.im : ℂ) * Complex.I - u) * (L : ℂ)‖
        = ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ * L := by
      rw [norm_mul]
      rw [show ‖((L : ℝ) : ℂ)‖ = L from
        (RCLike.norm_ofReal L).trans (abs_of_pos hL)]
    rw [h2] at h
    have h3 : ‖(((a : ℝ)) : ℂ)‖ = a :=
      (RCLike.norm_ofReal a).trans (abs_of_pos ha)
    rw [h3] at h
    nlinarith only [h, hfar, hL]
  have hhalf : δ * L / 2 ≤ ‖(s - u) * (L : ℂ)‖ := by linarith only [hnorm, haδ]
  have hpos : 0 < ‖(s - u) * (L : ℂ)‖ := by linarith only [hhalf, hδL, ha, haδ, hnorm]
  set w : ℝ := (a + lam₁) / ‖(s - u) * (L : ℂ)‖ with hw
  have hw0 : 0 ≤ w := div_nonneg hα hpos.le
  have hw1 : w ≤ 1 := by
    rw [hw, div_le_one hpos]
    linarith only [hhalf, hαδ, haδ, hnorm]
  have hw2 : w ≤ 2 * (a + lam₁) / (δ * L) := by
    rw [hw, div_le_div_iff₀ hpos hδL]
    have h2 : δ * L ≤ 2 * ‖(s - u) * (L : ℂ)‖ := by linarith only [hhalf, haδ, hnorm]
    nlinarith only [hα, h2, ha, haδ, hnorm, hlam₁]
  have harg : ‖(a + lam₁) / ((s - u) * (L : ℂ))‖ = w := by
    rw [hw, norm_div, ← Complex.ofReal_add]
    rw [show ‖(((a + lam₁ : ℝ)) : ℂ)‖ = a + lam₁ from
      (RCLike.norm_ofReal (a + lam₁)).trans (abs_of_nonneg hα)]
  have hP3 : ‖Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))‖ ≤ (8 / 3) * w := by
    set z : ℂ := (a + lam₁) / ((s - u) * (L : ℂ)) with hz
    have h1 : ‖z‖ = w := harg
    have h2 : ‖z ^ 2‖ ≤ w := by
      rw [norm_pow, h1]
      calc w ^ 2 = w * w := by ring
        _ ≤ w * 1 := mul_le_mul_of_nonneg_left hw1 hw0
        _ = w := by ring
    have h3 : ‖(2 / 3 : ℂ) * z ^ 3‖ ≤ (2 / 3) * w := by
      rw [show (2 / 3 : ℂ) = (((2 : ℝ) / 3 : ℝ) : ℂ) by push_cast; ring]
      rw [norm_mul, norm_pow, h1]
      rw [show ‖(((2 : ℝ) / 3 : ℝ) : ℂ)‖ = 2 / 3 from
        (RCLike.norm_ofReal ((2:ℝ)/3)).trans
          (abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3))]
      have hw3 : w ^ 3 ≤ w := by
        calc w ^ 3 = w ^ 2 * w := by ring
          _ ≤ 1 * w := mul_le_mul_of_nonneg_right (by nlinarith only [hw0, hw1]) hw0
          _ = w := by ring
      linarith only [hw3, hw0]
    calc ‖Work.ZeroFreeTables.P3 z‖ = ‖z + z ^ 2 + (2 / 3) * z ^ 3‖ := by
          rw [Work.ZeroFreeTables.P3]
      _ ≤ ‖z + z ^ 2‖ + ‖(2 / 3) * z ^ 3‖ := norm_add_le _ _
      _ ≤ (‖z‖ + ‖z ^ 2‖) + ‖(2 / 3) * z ^ 3‖ := by linarith only [norm_add_le z (z ^ 2)]
      _ ≤ (w + w) + (2 / 3) * w := by linarith only [h1, h2, h3, harg]
      _ = (8 / 3) * w := by ring
  have hfinal : (8 / 3) * w ≤ 8 * (a + lam₁) / (δ * L) := by
    have h1 : (8 / 3) * w ≤ (8 / 3) * (2 * (a + lam₁) / (δ * L)) :=
      mul_le_mul_of_nonneg_left hw2 (by norm_num)
    have h2 : (8 / 3) * (2 * (a + lam₁) / (δ * L)) = (16 / 3) * (a + lam₁) / (δ * L) := by ring
    have h3 : (16 / 3) * (a + lam₁) / (δ * L) ≤ 8 * (a + lam₁) / (δ * L) := by
      have h4 : (0 : ℝ) ≤ (a + lam₁) / (δ * L) := div_nonneg hα hδL.le
      have h5 : (16 / 3 : ℝ) ≤ 8 := by norm_num
      calc (16 / 3) * (a + lam₁) / (δ * L) = (16 / 3) * ((a + lam₁) / (δ * L)) := by ring
        _ ≤ 8 * ((a + lam₁) / (δ * L)) := mul_le_mul_of_nonneg_right h5 h4
        _ = 8 * (a + lam₁) / (δ * L) := by ring
    linarith only [h1, h2, h3, hw2]
  calc |(Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re|
      ≤ ‖Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))‖ := Complex.abs_re_le_norm _
    _ ≤ 8 * (a + lam₁) / (δ * L) := le_trans hP3 hfinal
/-! ## Extraction: a single zero's `P₃`-term is dominated by the near sum -/

/-- Points within `δ ≤ 1` of `1 + i·Im s` lie in the closed ball of radius `|s.im| + 2`. -/
private lemma mem_closedBall_of_near {s u : ℂ} {δ : ℝ} (hδ1 : δ ≤ 1)
    (hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :
    u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have h3 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ≤ 1 + |s.im| := by
    calc ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖
        ≤ ‖(1 : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 + |s.im| := by simp
  calc ‖u‖ ≤ ‖u - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖
              + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by
        have hh := norm_add_le (u - ((1 : ℂ) + (s.im : ℂ) * Complex.I))
          ((1 : ℂ) + (s.im : ℂ) * Complex.I)
        simpa using hh
    _ = ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖
              + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by rw [norm_sub_rev]
    _ ≤ δ + (1 + |s.im|) := by linarith only [hnear, h3]
    _ ≤ 1 + (1 + |s.im|) := by linarith only [hδ1]
    _ = |s.im| + 2 := by ring

/-- The near `P₃` summand is summable: its support lies in the ball in which the divisor of
the completed `L`-function has finite support. -/
theorem nearP3summand_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {L a lam₁ δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {s : ℂ} :
    Summable (fun v : ℂ => Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ v) := by
  classical
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hfinDiv : (Function.support (fun u : ℂ => MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) u)).Finite := by
    simpa [Function.HasFiniteSupport] using
      (MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ)
        (U := Metric.closedBall (0 : ℂ) (|s.im| + 2))
        (V := Metric.closedBall (0 : ℂ) (|s.im| + 2))
        hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) (|s.im| + 2)) (le_refl _))
  refine summable_of_ne_finset_zero (s := hfinDiv.toFinset) ?_
  intro v hv
  have hdiv0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) v = 0 := by
    by_contra hne
    exact hv (by rw [Set.Finite.mem_toFinset, Function.mem_support]; exact hne)
  by_cases hball : v ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)
  · have hzm0 : Work.LinnikContract.zeroMult χ v = 0 := by
      have hqr : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (|s.im| + 2)) v
          = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v : ℤ) := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hball]
        simp only [analyticOrderNatAt]
        cases h : analyticOrderAt (DirichletCharacter.completedLFunction χ) v with
        | top => simp
        | coe n => simp
      have hzero : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v = 0 := by
        have : (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) v : ℤ) = 0 := by
          rw [← hqr]; exact hdiv0
        exact_mod_cast this
      rw [Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim v]
      exact hzero
    rw [Work.ZeroFreeTables.P9.nearP3summand, hzm0]
    ring
  · have hni : Work.ZeroFreeTables.P9.nearInd s δ v = 0 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg]
      intro hc
      exact hball (mem_closedBall_of_near hδ1 hc)
    rw [Work.ZeroFreeTables.P9.nearP3summand, hni]
    ring

/-- **Extraction of a zero in the window.**  If `u` is a zero with `|u.im| ≤ 10`,
`λ₁ ≤ λ(u)` and `u` inside the `δ`-window of `1 + i·Im s`, then its `P₃`-term is at most the
near `P₃` sum. -/
theorem nearP3sum_ge_P3term {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {L a lam₁ δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hδ : 0 < δ) (hδ1 : δ < 1) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 3)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
      lam₁ ≤ (1 - u.re) * L)
    {u : ℂ} (hzu : Work.LinnikContract.zeroMult χ u ≠ 0)
    (hlu : lam₁ ≤ (1 - u.re) * L)
    (hwin : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :
    (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      ≤ Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ := by
  have hsumm := nearP3summand_summable χ hχ hprim (L := L) (a := a) (lam₁ := lam₁) hδ (le_of_lt hδ1)
    (s := s)
  have hnn := Work.ZeroFreeTables.P9.nearP3summand_nonneg χ hL ha hlam₁ hδ1 hsre hsim hmin
  have h1 : Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u
      ≤ Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ := by
    rw [Work.ZeroFreeTables.P9.nearP3sum_eq_tsum]
    exact Summable.le_tsum hsumm u (fun j _ => hnn j)
  rw [Work.ZeroFreeTables.P9.nearP3summand_eq_P3] at h1
  have hind : Work.ZeroFreeTables.P9.nearInd s δ u = 1 := by
    rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hwin]
  rw [hind, mul_one] at h1
  have hzm1 : (1 : ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) :=
    mod_cast Nat.one_le_iff_ne_zero.mpr hzu
  have hP3nn : 0 ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
    Work.ZeroFreeTables.P9.P3term_nonneg_of_min hL ha hlam₁ hsre hlu
  calc (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
      = 1 * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by ring
    _ ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
          * (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re :=
        mul_le_mul_of_nonneg_right hzm1 hP3nn
    _ ≤ Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ := h1

/-- **Extraction with the far cost.**  For any zero `u` with `|u.im| ≤ 10` (and the
minimality hypothesis), the `P₃`-term of `u` is at most the near sum plus the far cost
`8α/(δL)`. -/
theorem nearP3sum_ge_P3term_sub {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {L a lam₁ δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hδ : 0 < δ) (hδ1 : δ < 1) (haδL : 2 * a ≤ δ * L) (hαδL : 2 * (a + lam₁) ≤ δ * L)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 3)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
      lam₁ ≤ (1 - u.re) * L)
    {u : ℂ} (hzu : Work.LinnikContract.zeroMult χ u ≠ 0) :
    (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        - 8 * (a + lam₁) / (δ * L)
      ≤ Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ := by
  by_cases hwin : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · have him : |u.im| ≤ 10 := by
      have h2 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
      have h1 : |s.im - u.im| ≤ δ := by
        have h1' := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
        rw [h2] at h1'
        exact h1'.trans hwin
      have h3 : |u.im| ≤ |s.im| + |s.im - u.im| := by
        calc |u.im| = |s.im - (s.im - u.im)| := by congr 1; ring
          _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
      linarith only [hδ, hδ1, hsim, h1, h3]
    have hlu : lam₁ ≤ (1 - u.re) * L := hmin u hzu him
    have h1 := nearP3sum_ge_P3term χ hχ hprim hL ha hlam₁ hδ hδ1 hsre hsim hmin hzu hlu hwin
    have h2 : (0 : ℝ) ≤ 8 * (a + lam₁) / (δ * L) := by positivity
    linarith
  · have hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := lt_of_not_ge hwin
    have h1 := P3term_abs_le_of_far hL ha hlam₁ hδ haδL hαδL hsre hfar
    have h2 : 0 ≤ Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ := by
      rw [Work.ZeroFreeTables.P9.nearP3sum_eq_tsum]
      refine tsum_nonneg (fun v => ?_)
      exact Work.ZeroFreeTables.P9.nearP3summand_nonneg χ hL ha hlam₁ hδ1 hsre hsim hmin v
    have h3 : (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ 8 * (a + lam₁) / (δ * L) := (abs_le.mp h1).2
    linarith [h2, h3]


end Work.ZeroFreeTables.Table4
