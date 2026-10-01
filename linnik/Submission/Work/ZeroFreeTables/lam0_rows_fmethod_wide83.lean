/-
Workaround module: verbatim copy of `Submission/Work/ZeroFreeTables/lam0w/HBLemma8_3_wide.lean`
(the team's proof of HB Lemma 8.3 in the wide/minimality form) with the redundant
`Table4.HB83_args` import removed -- `HB83_args` currently fails to compile because it
re-declares `Table4.P3AB_neg`, which is already in `Table4.HB83`, and `Table4.HB83` is
already in scope here through `Table4.HB83_base`.  The three declarations are renamed
(`fmErrBound`, `fmPointBound`, `HBLemma8_3_wide_fm`) so that this module can coexist with
the original.  No mathematical content is added or changed.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Table4.HB83_base
import Submission.Work.ZeroFreeTables.Table4.Engine8A
import Submission.Work.ZeroFreeTables.Table4.zeroMult_conj
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Work.ZeroFreeTables.lam0w.FarBound
import Submission.Work.ZeroFreeTables.lam0w.Bounds
import Submission.Work.ZeroFreeTables.lam0_fm_near3
import Submission.Work.ZeroFreeTables.lam0_fm_principalBound
import Submission.Work.ZeroFreeTables.lam0w.imprimCorr4

set_option maxHeartbeats 16000000
open Complex DirichletCharacter
open scoped BigOperators
noncomputable section
namespace Work.ZeroFreeTables.lam0w

theorem fmErrBound {a lam1 L δ J Ct e3 Zc Zc2 card : ℝ}
    (ha : 0 < a) (hlam1 : 0 ≤ lam1) (hlam_a : lam1 ≤ a) (hL1 : 1 ≤ L) (he3 : 0 < e3)
    (hJ : 0 ≤ J) (hCt : 0 ≤ Ct) (hδ : 0 < δ)
    (hZc0 : 0 ≤ Zc) (hZc20 : 0 ≤ Zc2) (hcard : card ≤ 3)
    (hZc : (1 + 4 / δ ^ 2) * J + Ct ≤ Zc * L)
    (hZc2 : (2 / δ) * (1 + 4 / δ ^ 2) * J + Ct ≤ Zc2 * L)
    (hK0 : 2 * a * Zc + (2 / 3) * (2 * a) ^ 2 * Zc2 + 24 / δ ≤ e3 * L) :
    ((a + lam1) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * J + Ct)
      + (2 / 3) * ((a + lam1) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct)
      + card * (8 * (a + lam1) / (δ * L)) ≤ (a + lam1) * e3 := by
  have hα0 : 0 < a + lam1 := by linarith
  have hα2a : a + lam1 ≤ 2 * a := by linarith
  have hLpos : 0 < L := by linarith
  have t1 : ((a + lam1) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * J + Ct)
      ≤ (a + lam1) * (2 * a * Zc / L) := by
    have e : ((a + lam1) ^ 2 / L ^ 2) * (Zc * L) = (a + lam1) * (a + lam1) * Zc / L := by
      field_simp <;> ring
    have h1 : ((a + lam1) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * J + Ct)
        ≤ ((a + lam1) ^ 2 / L ^ 2) * (Zc * L) :=
      mul_le_mul_of_nonneg_left hZc (by positivity)
    rw [e] at h1
    have h2 : (a + lam1) * (a + lam1) * Zc / L ≤ (a + lam1) * (2 * a * Zc / L) := by
      have hcore : (a + lam1) * Zc / L ≤ 2 * a * Zc / L := by
        apply div_le_div_of_nonneg_right _ hLpos.le
        nlinarith [hZc0, hα2a]
      have h3 : (a + lam1) * (a + lam1) * Zc / L = (a + lam1) * ((a + lam1) * Zc / L) := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left hcore hα0.le
    linarith [h1, h2]
  have t2 : (2 / 3) * ((a + lam1) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct)
      ≤ (a + lam1) * ((2 / 3) * (2 * a) ^ 2 * Zc2 / L) := by
    have e : (2 / 3) * ((a + lam1) ^ 3 / L ^ 3) * (Zc2 * L)
        = (a + lam1) * ((2 / 3) * (a + lam1) ^ 2 * Zc2 / L ^ 2) := by
      field_simp <;> ring
    have h1 : (2 / 3) * ((a + lam1) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct)
        ≤ (2 / 3) * ((a + lam1) ^ 3 / L ^ 3) * (Zc2 * L) :=
      mul_le_mul_of_nonneg_left hZc2 (by positivity)
    rw [e] at h1
    have hcore : (a + lam1) ^ 2 * Zc2 / L ^ 2 ≤ (2 * a) ^ 2 * Zc2 / L := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < L ^ 2)]
      have hsq : (a + lam1) ^ 2 ≤ (2 * a) ^ 2 := by nlinarith [hα0, hα2a]
      have e2 : (2 * a) ^ 2 * Zc2 / L * L ^ 2 = (2 * a) ^ 2 * Zc2 * L := by field_simp <;> ring
      rw [e2]
      have h2a : (0:ℝ) ≤ (2 * a) ^ 2 := by positivity
      have hstep : (a + lam1) ^ 2 * Zc2 ≤ (2 * a) ^ 2 * Zc2 :=
        mul_le_mul_of_nonneg_right hsq hZc20
      have hx : 0 ≤ (2 * a) ^ 2 * Zc2 := mul_nonneg h2a hZc20
      have hstep2 : (2 * a) ^ 2 * Zc2 ≤ (2 * a) ^ 2 * Zc2 * L := by
        calc (2 * a) ^ 2 * Zc2 = (2 * a) ^ 2 * Zc2 * 1 := by ring
          _ ≤ (2 * a) ^ 2 * Zc2 * L := mul_le_mul_of_nonneg_left hL1 hx
      linarith [hstep, hstep2]
    have h3 : (a + lam1) * ((2 / 3) * (a + lam1) ^ 2 * Zc2 / L ^ 2)
        ≤ (a + lam1) * ((2 / 3) * (2 * a) ^ 2 * Zc2 / L) := by
      apply mul_le_mul_of_nonneg_left _ hα0.le
      calc (2 / 3) * (a + lam1) ^ 2 * Zc2 / L ^ 2
          = (2 / 3) * ((a + lam1) ^ 2 * Zc2 / L ^ 2) := by ring
        _ ≤ (2 / 3) * ((2 * a) ^ 2 * Zc2 / L) :=
            mul_le_mul_of_nonneg_left hcore (by norm_num)
        _ = (2 / 3) * (2 * a) ^ 2 * Zc2 / L := by ring
    linarith [h1, h3]
  have t3 : card * (8 * (a + lam1) / (δ * L)) ≤ (a + lam1) * (24 / δ / L) := by
    have h1 : 8 * (a + lam1) / (δ * L) = (a + lam1) * (8 / δ / L) := by
      field_simp
    rw [h1]
    have h2 : card * ((a + lam1) * (8 / δ / L)) ≤ 3 * ((a + lam1) * (8 / δ / L)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have h3 : 3 * ((a + lam1) * (8 / δ / L)) = (a + lam1) * (24 / δ / L) := by ring
    linarith [h2, h3]
  have hsum : ((a + lam1) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * J + Ct)
      + (2 / 3) * ((a + lam1) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct)
      + card * (8 * (a + lam1) / (δ * L))
      ≤ (a + lam1) * (2 * a * Zc / L) + (a + lam1) * ((2 / 3) * (2 * a) ^ 2 * Zc2 / L)
        + (a + lam1) * (24 / δ / L) := by linarith [t1, t2, t3]
  have hfin : (a + lam1) * (2 * a * Zc / L) + (a + lam1) * ((2 / 3) * (2 * a) ^ 2 * Zc2 / L)
      + (a + lam1) * (24 / δ / L) ≤ (a + lam1) * e3 := by
    have e : (a + lam1) * (2 * a * Zc / L) + (a + lam1) * ((2 / 3) * (2 * a) ^ 2 * Zc2 / L)
        + (a + lam1) * (24 / δ / L)
        = (a + lam1) * ((2 * a * Zc + (2 / 3) * (2 * a) ^ 2 * Zc2 + 24 / δ) / L) := by
      field_simp <;> ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hα0.le
    rw [div_le_iff₀ hLpos]
    linarith [hK0]
  linarith [hsum, hfin]

theorem fmPointBound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {L a lam₁ δ c e Ct J : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 4)
    (hlog : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L)
    (par : ℕ) (hpar0 : χ.Even → par = 0) (hpar1 : χ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hJ : Work.ZeroFreeTables.P9.invSqSum N χ s ≤ J)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
      lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult χ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ 10)
    (hE : ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * J + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct)
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) ≤ (a + lam₁) * e) :
    Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      ≤ -(∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re)
        + (a + lam₁) * (c + e) := by
  have h1 := Work.ZeroFreeTables.Table4.engine8 χ hχ hprim ha hlam₁ hδ hδ1 hLt haδL hsre
    (le_trans hsim (by norm_num)) hlog par hpar0 hpar1 hS2 hS3
  have h2 := nearP3sum_ge_kept_four_fm χ hχ (by linarith : (0:ℝ) < L) ha hlam₁ hδ hδ1 haδL hsre hsim
    hmin T hT hTim
  have hw : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by positivity
  have hc1 : ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      ≤ ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * J + Ct) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [mul_le_mul_of_nonneg_left hJ hw]
  have hc2 : (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3)
        * ((2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      ≤ (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * J + Ct) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hw2 : (0 : ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2) := by positivity
    linarith [mul_le_mul_of_nonneg_left hJ hw2]
  linarith [h1, h2, hc1, hc2, hE]

theorem HBLemma8_3_wide_fm : ∀ (a K ε : ℝ), 0 < a → 1 / 4 ≤ K → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 →
      Work.LinnikContract.IsZ χ₁ ρ₁ → Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ 2 →
      ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 →
      Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ →
      Work.ZeroFreeTables.cond86 (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) a →
      0 ≤ Work.ZeroFreeTables.p83 (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) a K
        + (K + 1) ^ 2 * (a + Work.LinnikContract.lamOf q ρ₁) * ε := by
  intro a K ε ha hK hε
  have hε8 : (0:ℝ) < ε/8 := by linarith
  have hε2 : (0:ℝ) < ε/2 := by linarith
  obtain ⟨Ld, δ, hδ0, hδ1, hLd⟩ := Work.ZeroFreeTables.Table4.logDerivHyp_eighth (e := ε/8) hε8
  obtain ⟨CJ, hCJ0, hCJ⟩ := invSqSum_uniform
  obtain ⟨Ct, hCt0, hCtp⟩ := paritySumBound
  obtain ⟨Lp, hLp⟩ := principalBound4_fm (a := a) ha hε8
  obtain ⟨Li, hLi⟩ := imprimCorr4 (a := a) ha hε8
  set c2 : ℝ := Real.log (2 + Real.sqrt ((1 + a) ^ 2 + 16)) + 2 with hc2
  have hc2nn : 0 ≤ c2 := by
    rw [hc2]
    have h : (0:ℝ) ≤ Real.log (2 + Real.sqrt ((1+a)^2 + 16)) :=
      Real.log_nonneg (by have := Real.sqrt_nonneg ((1+a)^2 + 16); linarith)
    linarith
  set Wc : ℝ := (1 + 4 / δ ^ 2) * CJ * (1 + c2) + Ct with hWc
  set Wc2 : ℝ := (2 / δ) * (1 + 4 / δ ^ 2) * CJ * (1 + c2) + Ct with hWc2
  have hWc0 : 0 ≤ Wc := by rw [hWc]; positivity
  have hWc20 : 0 ≤ Wc2 := by rw [hWc2]; positivity
  set K0 : ℝ := 2 * a * Wc + (2 / 3) * (2 * a) ^ 2 * Wc2 + 24 / δ with hK0def
  have key : ∀ T : ℝ, ∃ N : ℕ, ∀ q : ℕ, N ≤ q → T ≤ Real.log (q:ℝ) := by
    intro T
    refine ⟨Nat.ceil (Real.exp T), fun q hq => ?_⟩
    have h1 : Real.exp T ≤ (q:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hq)
    rw [← Real.log_exp T]
    exact Real.log_le_log (Real.exp_pos T) h1
  obtain ⟨qb, hqb⟩ := key 4
  obtain ⟨qa, hqa⟩ := key (Real.exp a)
  obtain ⟨qb2, hqb2⟩ := key (Real.exp (1/a))
  obtain ⟨qc, hqc⟩ := key (2*a/δ)
  obtain ⟨qd, hqd⟩ := key Ld
  obtain ⟨qp, hqp⟩ := key Lp
  obtain ⟨qi, hqi⟩ := key Li
  obtain ⟨qe, hqe⟩ := key (K0/(ε/2))
  refine ⟨max (max (max qb qa) (max qb2 qc)) (max (max qd qp) (max qi qe)) + 3, ?_⟩
  intro q hq hqne χ₁ ρ₁ ρ₀ hwide hsq hχ1 him1 hZ1 hzm0 him0abs hne him0 hlamle hcond
  classical
  letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hqb' : qb ≤ q := by omega
  have hqa' : qa ≤ q := by omega
  have hqb2' : qb2 ≤ q := by omega
  have hqc' : qc ≤ q := by omega
  have hqd' : qd ≤ q := by omega
  have hqp' : qp ≤ q := by omega
  have hqi' : qi ≤ q := by omega
  have hqe' : qe ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hL3 : (4:ℝ) ≤ Real.log (q:ℝ) := hqb q hqb'
  set L := Real.log (q:ℝ) with hLdef
  have hLile : Li ≤ L := by rw [hLdef]; exact hqi q hqi'
  have hLple : Lp ≤ L := by rw [hLdef]; exact hqp q hqp'
  have hlogqle : Real.log (q:ℝ) ≤ L := le_of_eq hLdef.symm

  -- ## the setting
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlogqpos : 0 < Real.log (q:ℝ) := by rw [← hLdef]; exact hLpos
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hLt : (1:ℝ) < L := by linarith
  have hq2 : 2 ≤ q := by omega
  -- lam1 ≥ 0 and lam1 ≤ a
  have hlam1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hZ1
  have hlam0nn : 0 ≤ Work.LinnikContract.lamOf q ρ₀ := by
    have hstrip : 0 < ρ₀.re ∧ ρ₀.re < 1 := by
      have hchi1' : χ₁.primitiveCharacter ≠ 1 := by
        intro h1
        refine hχ1 ?_
        rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h1,
          DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level]
      have hz : DirichletCharacter.completedLFunction χ₁.primitiveCharacter ρ₀ = 0 := by
        apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
        simpa [Work.LinnikContract.zeroMult] using hzm0
      exact Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter hchi1'
        (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hz
    rw [Work.LinnikContract.lamOf]
    exact mul_nonneg (by linarith [hstrip.2]) (le_of_lt hlogqpos)
  have hlam1lea : Work.LinnikContract.lamOf q ρ₁ ≤ a := by
    have ha1 : 0 < a + Work.LinnikContract.lamOf q ρ₁ := by linarith
    have ha0 : 0 < a + Work.LinnikContract.lamOf q ρ₀ := by linarith
    have hle1 : 1/(a + Work.LinnikContract.lamOf q ρ₀)^3
        ≤ 1/(a + Work.LinnikContract.lamOf q ρ₁)^3 := by
      apply one_div_le_one_div_of_le (pow_pos ha1 3)
      exact pow_le_pow_left₀ ha1.le (by linarith) 3
    unfold Work.ZeroFreeTables.cond86 at hcond
    have h2 : 1/a^3 ≤ 2/(a + Work.LinnikContract.lamOf q ρ₁)^3 := by
      have e : (2:ℝ)/(a + Work.LinnikContract.lamOf q ρ₁)^3
          = 1/(a + Work.LinnikContract.lamOf q ρ₁)^3
            + 1/(a + Work.LinnikContract.lamOf q ρ₁)^3 := by ring
      rw [e]
      linarith [hcond, hle1]
    have hkey : (a + Work.LinnikContract.lamOf q ρ₁)^3 ≤ 2 * a^3 := by
      have h3 := (div_le_div_iff₀ (by positivity : (0:ℝ) < a^3)
        (by positivity : (0:ℝ) < (a + Work.LinnikContract.lamOf q ρ₁)^3)).mp h2
      linarith [h3]
    have hma : a + Work.LinnikContract.lamOf q ρ₁ ≤ 2 * a := by
      by_contra hcon
      simp only [not_le] at hcon
      have h1 : (2*a)^3 < (a + Work.LinnikContract.lamOf q ρ₁)^3 :=
        pow_lt_pow_left₀ hcon (by linarith : (0:ℝ) ≤ 2*a) (by norm_num : (3:ℕ) ≠ 0)
      have hcube : (a + Work.LinnikContract.lamOf q ρ₁)^3 ≤ (2*a)^3 := by nlinarith [hkey, ha]
      linarith [h1, hcube]
    linarith [hma]
  have hδ := hδ0
  have hα0 : 0 < a + Work.LinnikContract.lamOf q ρ₁ := by linarith
  have hα2a : a + Work.LinnikContract.lamOf q ρ₁ ≤ 2 * a := by linarith
  have haδL : 2 * a ≤ δ * L := by
    have := hqc q hqc'
    rw [hLdef]
    -- 2a/δ ≤ log q
    rw [div_le_iff₀ hδ0] at this
    linarith [this]
  -- ## the primitive character
  have hprim : (χ₁.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ₁
  have hchi1 : χ₁.primitiveCharacter ≠ 1 := by
    intro h1
    refine hχ1 ?_
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h1,
      DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level]
  have hchisq : (χ₁.primitiveCharacter) ^ 2 = 1 := by
    have hcl := DirichletCharacter.changeLevel_primitiveCharacter χ₁
    refine DirichletCharacter.changeLevel_injective χ₁.conductor_dvd_level ?_
    rw [map_pow, hcl, hsq, map_one]
  have hzeroM : ∀ u : ℂ, Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u
      = Work.LinnikContract.zeroMult χ₁ u := by
    intro u
    rw [Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
      (χ₁.primitiveCharacter) hprim u]
    rfl
  have hcond_le : χ₁.conductor ≤ q := Nat.le_of_dvd (by omega) χ₁.conductor_dvd_level
  have hlogNle : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ₁.conductor_ne_zero)
      (by exact_mod_cast hcond_le)
  have hLdle : Ld ≤ L := hqd q hqd'
  have hlogHyp : Work.ZeroFreeTables.LogDerivHyp (χ₁.primitiveCharacter) δ L (1/8 + ε/8) :=
    hLd (χ := χ₁.primitiveCharacter) hchi1 hprim hchisq hLdle hlogNle
  have hminChi : ∀ u : ℂ, Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u ≠ 0 →
      |u.im| ≤ 10 → Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro u hzu him
    have hzu1 : Work.LinnikContract.zeroMult χ₁ u ≠ 0 := by rw [← hzeroM u]; exact hzu
    have hle := hwide.2 χ₁ u hχ1 hzu1 him
    rw [Work.LinnikContract.lamOf] at hle ⊢
    rw [hLdef]
    exact hle
  -- log L ≥ a and log L ≥ 1/a
  have hlogLa : a ≤ Real.log L := by
    have h1 : Real.exp a ≤ L := hqa q hqa'
    calc a = Real.log (Real.exp a) := (Real.log_exp a).symm
      _ ≤ Real.log L := Real.log_le_log (Real.exp_pos a) h1
  have hlogLib : 1/a ≤ Real.log L := by
    have h1 : Real.exp (1/a) ≤ L := hqb2 q hqb2'
    calc 1/a = Real.log (Real.exp (1/a)) := (Real.log_exp (1/a)).symm
      _ ≤ Real.log L := Real.log_le_log (Real.exp_pos (1/a)) h1
  have hlogLpos : 0 < Real.log L := by
    have : 0 < 1/a := by positivity
    linarith
  -- ## per-point facts
  set sig : ℝ := 1 + a / L with hsig
  set gam : ℝ := ρ₀.im with hgam
  have hgam2 : |gam| ≤ 2 := by rw [hgam]; exact him0abs
  set mu : ℝ := gam * L with hmu
  set al : ℝ := a + Work.LinnikContract.lamOf q ρ₁ with hal
  have hal_eq : al = a + Work.LinnikContract.lamOf q ρ₁ := hal
  have hs0re : ((sig : ℂ)).re = 1 + a / L := by simp [sig]
  have hs1re : (((sig : ℂ) + (gam : ℂ) * Complex.I)).re = 1 + a / L := by simp [sig]
  have hs2re : (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I)).re = 1 + a / L := by simp [sig]
  have hs0im : |((sig : ℂ)).im| ≤ 4 := by simp
  have hs1im : |(((sig : ℂ) + (gam : ℂ) * Complex.I)).im| ≤ 4 := by
    have : (((sig : ℂ) + (gam : ℂ) * Complex.I)).im = gam := by simp
    rw [this]; linarith [hgam2]
  have hs2im : |(((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I)).im| ≤ 4 := by
    have h1 : (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I)).im = 2 * gam := by simp
    rw [h1, abs_mul]
    have : |(2:ℝ)| = 2 := by norm_num
    rw [this]; linarith [hgam2]
  have hparle : (if (χ₁.primitiveCharacter).Even then (0:ℕ) else 1) ≤ 1 := by split <;> omega
  have hpar0 : (χ₁.primitiveCharacter).Even → (if (χ₁.primitiveCharacter).Even then (0:ℕ) else 1) = 0 := by
    intro h; simp [h]
  have hpar1 : (χ₁.primitiveCharacter).Odd → (if (χ₁.primitiveCharacter).Even then 0 else 1) = 1 := by
    intro h
    have hne : ¬ (χ₁.primitiveCharacter).Even := by
      intro he
      have h1 : (χ₁.primitiveCharacter) (-1) = 1 := he
      have h2 : (χ₁.primitiveCharacter) (-1) = -1 := h
      rw [h1] at h2; norm_num at h2
    simp [hne]
  -- nearInvHyp at a point
  have hlogOf : ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 4 →
      (-logDeriv (DirichletCharacter.LFunction (χ₁.primitiveCharacter)) s).re
        + Work.ZeroFreeTables.P9.nearInvSum (χ₁.conductor) (χ₁.primitiveCharacter) s δ
        ≤ (1/8 + ε/8) * L := by
    intro s hre him
    have h := hlogHyp s ?_ ?_ ?_
    · have e := Work.ZeroFreeTables.P9.invNearSum_eq_tsum (χ₁.primitiveCharacter) hchi1 hprim
        (le_trans him (by norm_num) : |s.im| ≤ 10) hδ0 (le_of_lt hδ1)
      rw [e] at h
      exact h
    · rw [hre]
      have h1 : 1 ≤ a * Real.log L := by
        have := hlogLib; rw [div_le_iff₀ ha] at this; linarith
      have h2 : 1/(L * Real.log L) ≤ a/L := by
        rw [div_le_div_iff₀ (mul_pos hLpos hlogLpos) hLpos]
        nlinarith [h1, hLpos]
      linarith
    · rw [hre]
      have h2 : a/L ≤ Real.log L / L := by
        rw [div_le_div_iff₀ hLpos hLpos]; nlinarith [hlogLa]
      linarith
    · linarith [him, hL3]
  -- invSqSum bound
  have hJOf : ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 4 →
      Work.ZeroFreeTables.P9.invSqSum (χ₁.conductor) (χ₁.primitiveCharacter) s
        ≤ CJ * (L + c2) := by
    intro s hre him
    have h1 := hCJ (χ := χ₁.primitiveCharacter) hchi1 hprim s
    have hnorm : ‖s‖ ≤ Real.sqrt ((1 + a) ^ 2 + 16) := by
      have hsr : s.re ≤ 1 + a := by
        rw [hre]
        have h2 : a / L ≤ a := by rw [div_le_iff₀ hLpos]; nlinarith [hL1, ha]
        linarith
      have hsq : ‖s‖ ^ 2 ≤ (1 + a) ^ 2 + 16 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have hsr0 : 0 ≤ s.re := by rw [hre]; positivity
        have him2 : s.im ^ 2 ≤ 16 := by have := abs_le.mp him; nlinarith
        nlinarith [hsr, hsr0, him2]
      calc ‖s‖ = Real.sqrt (‖s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg s)).symm
        _ ≤ Real.sqrt ((1 + a) ^ 2 + 16) := Real.sqrt_le_sqrt hsq
    have hlog2 : Real.log (2 + ‖s‖) + 2 ≤ c2 := by
      have hle : 2 + ‖s‖ ≤ 2 + Real.sqrt ((1 + a) ^ 2 + 16) := by linarith
      have h3 := Real.log_le_log (by positivity : (0:ℝ) < 2 + ‖s‖) hle
      rw [hc2]; linarith [h3]
    have h2 : Real.log ((χ₁.conductor : ℕ) : ℝ) + Real.log (2 + ‖s‖) + 2 ≤ L + c2 := by
      linarith [hlogNle, hlog2]
    have h3 : CJ * (Real.log ((χ₁.conductor : ℕ) : ℝ) + Real.log (2 + ‖s‖) + 2) ≤ CJ * (L + c2) :=
      mul_le_mul_of_nonneg_left h2 hCJ0.le
    linarith [h1, h3]
  -- the error bound
  have hEOf : ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 4 → ∀ (T : Finset ℂ), T.card ≤ 3 →
      ((a + Work.LinnikContract.lamOf q ρ₁) ^ 2 / L ^ 2)
          * ((1 + 4 / δ ^ 2) * (CJ * (L + c2)) + Ct)
        + (2 / 3) * ((a + Work.LinnikContract.lamOf q ρ₁) ^ 3 / L ^ 3)
          * ((2 / δ) * (1 + 4 / δ ^ 2) * (CJ * (L + c2)) + Ct)
        + (T.card : ℝ) * (8 * (a + Work.LinnikContract.lamOf q ρ₁) / (δ * L))
        ≤ (a + Work.LinnikContract.lamOf q ρ₁) * (ε / 2) := by
    intro s hre him T hcard
    refine fmErrBound ha hlam1nn hlam1lea hL1 hε2 ?_ ?_ hδ0 hWc0 hWc20 (by exact_mod_cast hcard) ?_ ?_ ?_
    · exact mul_nonneg hCJ0.le (by positivity)
    · exact hCt0.le
    · rw [hWc]
      have hLc : L + c2 ≤ (1 + c2) * L := by nlinarith [hL1, hc2nn]
      have h1 : (1 + 4 / δ ^ 2) * (CJ * (L + c2)) ≤ (1 + 4 / δ ^ 2) * (CJ * ((1 + c2) * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hLc hCJ0.le
      have h2 : Ct ≤ Ct * L := by
        calc Ct = Ct * 1 := by ring
          _ ≤ Ct * L := mul_le_mul_of_nonneg_left hL1 hCt0.le
      have h3 : (1 + 4 / δ ^ 2) * (CJ * ((1 + c2) * L)) + Ct * L
          = ((1 + 4 / δ ^ 2) * CJ * (1 + c2) + Ct) * L := by ring
      linarith [h1, h2, h3]
    · rw [hWc2]
      have hLc : L + c2 ≤ (1 + c2) * L := by nlinarith [hL1, hc2nn]
      have h1 : (2 / δ) * (1 + 4 / δ ^ 2) * (CJ * (L + c2))
          ≤ (2 / δ) * (1 + 4 / δ ^ 2) * (CJ * ((1 + c2) * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hLc hCJ0.le
      have h2 : Ct ≤ Ct * L := by
        calc Ct = Ct * 1 := by ring
          _ ≤ Ct * L := mul_le_mul_of_nonneg_left hL1 hCt0.le
      have h3 : (2 / δ) * (1 + 4 / δ ^ 2) * (CJ * ((1 + c2) * L)) + Ct * L
          = ((2 / δ) * (1 + 4 / δ ^ 2) * CJ * (1 + c2) + Ct) * L := by ring
      linarith [h1, h2, h3]
    · have := hqe q hqe'
      rw [← hLdef, div_le_iff₀ hε2] at this
      linarith [this, hK0def]
  -- ## reduced-fraction facts
  have hlam1eq : Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * L := by
    rw [Work.LinnikContract.lamOf, hLdef]
  have hlam0eq : Work.LinnikContract.lamOf q ρ₀ = (1 - ρ₀.re) * L := by
    rw [Work.LinnikContract.lamOf, hLdef]
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hρ₁re : ρ₁.re = 1 - Work.LinnikContract.lamOf q ρ₁ / L := by
    rw [hlam1eq]; field_simp <;> ring
  have hρ₀re : ρ₀.re = 1 - Work.LinnikContract.lamOf q ρ₀ / L := by
    rw [hlam0eq]; field_simp <;> ring
  have hconjre : (starRingEnd ℂ ρ₀).re = 1 - Work.LinnikContract.lamOf q ρ₀ / L := by
    rw [show (starRingEnd ℂ ρ₀).re = ρ₀.re by simp]
    exact hρ₀re
  have hne0c : ρ₀ ≠ starRingEnd ℂ ρ₀ := by
    intro h
    have h2 : ρ₀.im = -(ρ₀.im) := by have := congrArg Complex.im h; simpa using this
    exact him0 (by linarith [h2])
  have hne1c : ρ₁ ≠ starRingEnd ℂ ρ₀ := by
    intro h
    have h2 : ρ₁.im = -(ρ₀.im) := by have := congrArg Complex.im h; simpa using this
    rw [him1] at h2
    exact him0 (by linarith [h2])
  have hzr1 : Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) ρ₁ ≠ 0 := by
    rw [hzeroM ρ₁]; exact hZ1.2.1
  have hzr0 : Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) ρ₀ ≠ 0 := by
    rw [hzeroM ρ₀]; exact hzm0
  have hzrc : Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) (starRingEnd ℂ ρ₀) ≠ 0 := by
    rw [hzeroM (starRingEnd ℂ ρ₀), Work.ZeroFreeTables.Table4.zeroMult_conj χ₁ hsq ρ₀]
    exact hzm0
  have himr1 : |ρ₁.im| ≤ 10 := by rw [him1]; norm_num
  have himr0 : |ρ₀.im| ≤ 10 := by linarith [him0abs]
  have himrc : |(starRingEnd ℂ ρ₀).im| ≤ 10 := by
    rw [Complex.conj_im, abs_neg]; linarith [him0abs]
  -- ## retained-sum expansions
  have hT0s0 : ∑ u ∈ ({ρ₁, ρ₀} : Finset ℂ),
        (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)) / (((sig : ℂ) - u) * (L : ℂ)))).re
      = P3R 1 + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) mu := by
    rw [Finset.sum_pair hne.symm]
    have e1 : (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)) / (((sig : ℂ) - ρ₁) * (L : ℂ)))).re = P3R 1 := by
      rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := Work.LinnikContract.lamOf q ρ₁) hLne hs0re hρ₁re]
      rw [show (((sig : ℂ)).im - ρ₁.im) * L = 0 by simp [him1]]
      rw [Work.ZeroFreeTables.Table4.P3AB_zero, div_self (ne_of_gt hα0)]
    have e2 : (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)) / (((sig : ℂ) - ρ₀) * (L : ℂ)))).re
        = Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) mu := by
      rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := Work.LinnikContract.lamOf q ρ₀) hLne hs0re hρ₀re]
      rw [show (((sig : ℂ)).im - ρ₀.im) * L = -mu by simp [hmu, hgam]]
      rw [Work.ZeroFreeTables.Table4.P3AB_neg (a + Work.LinnikContract.lamOf q ρ₁)
        (a + Work.LinnikContract.lamOf q ρ₀) mu
        (by positivity : (0:ℝ) < a + Work.LinnikContract.lamOf q ρ₀)]
    rw [e1, e2]
  have hT0s2 : ∑ u ∈ ({ρ₁, ρ₀} : Finset ℂ),
        (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)) / (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I - u) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₁) (2 * mu)
        + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) mu := by
    rw [Finset.sum_pair hne.symm]
    congr 1
    · rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := Work.LinnikContract.lamOf q ρ₁) hLne hs2re hρ₁re]
      congr 1
      rw [show (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I).im - ρ₁.im) * L = 2 * mu by
        have h1 : (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I)).im = 2 * gam := by simp
        rw [h1, him1, hmu]; ring]
    · rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := Work.LinnikContract.lamOf q ρ₀) hLne hs2re hρ₀re]
      congr 1
      rw [show (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I).im - ρ₀.im) * L = mu by
        have h1 : (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I)).im = 2 * gam := by simp
        rw [h1, ← hgam, hmu]; ring]
  have hT1s1 : ∑ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ),
        (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)) / (((sig : ℂ) + (gam : ℂ) * Complex.I - u) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₁) mu
        + P3R ((a + Work.LinnikContract.lamOf q ρ₁) / (a + Work.LinnikContract.lamOf q ρ₀))
        + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) (2 * mu) := by
    rw [show ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ)
        = insert ρ₁ (insert ρ₀ {starRingEnd ℂ ρ₀}) by rfl]
    rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hne.symm, hne1c⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hne0c),
      Finset.sum_singleton]
    rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := Work.LinnikContract.lamOf q ρ₁) hLne hs1re hρ₁re]
    rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := Work.LinnikContract.lamOf q ρ₀) hLne hs1re hρ₀re]
    rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := Work.LinnikContract.lamOf q ρ₀) hLne hs1re hconjre]
    rw [show (((sig : ℂ) + (gam : ℂ) * Complex.I).im - ρ₁.im) * L = mu by
      have h1 : (((sig : ℂ) + (gam : ℂ) * Complex.I)).im = gam := by simp
      rw [h1, him1, hmu]; ring]
    rw [show (((sig : ℂ) + (gam : ℂ) * Complex.I).im - ρ₀.im) * L = 0 by
      have h1 : (((sig : ℂ) + (gam : ℂ) * Complex.I)).im = gam := by simp
      rw [h1, ← hgam]; ring]
    rw [Work.ZeroFreeTables.Table4.P3AB_zero]
    rw [show (((sig : ℂ) + (gam : ℂ) * Complex.I).im - (starRingEnd ℂ ρ₀).im) * L = 2 * mu by
      have h1 : (((sig : ℂ) + (gam : ℂ) * Complex.I)).im = gam := by simp
      have h2 : (starRingEnd ℂ ρ₀).im = -ρ₀.im := by simp [Complex.conj_im]
      rw [h1, h2, ← hgam, hmu]; ring]
    ring

  -- principal-side expansions
  have hP0 : (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)) / (((sig : ℂ) - 1) * (L : ℂ)))).re = P3R ((a + Work.LinnikContract.lamOf q ρ₁) / a) := by
    have : (1 : ℂ).re = 1 - (0:ℝ) / L := by simp
    rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := 0) hLne hs0re this]
    rw [show (((sig : ℂ)).im - (1 : ℂ).im) * L = 0 by simp]
    rw [Work.ZeroFreeTables.Table4.P3AB_zero]
    simp
  have hP1 : (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)) / (((sig : ℂ) + (gam : ℂ) * Complex.I - 1) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a mu := by
    have : (1 : ℂ).re = 1 - (0:ℝ) / L := by simp
    rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := 0) hLne hs1re this]
    have harg : (((sig : ℂ) + (gam : ℂ) * Complex.I).im - (1 : ℂ).im) * L = mu := by
      have h1 : (((sig : ℂ) + (gam : ℂ) * Complex.I)).im = gam := by simp
      rw [h1, Complex.one_im, hmu]; ring
    rw [harg]
    simp
  have hP2 : (Work.ZeroFreeTables.P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)) / (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I - 1) * (L : ℂ)))).re
      = Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a (2 * mu) := by
    have : (1 : ℂ).re = 1 - (0:ℝ) / L := by simp
    rw [reP3_div_eq_P3AB (al := Work.LinnikContract.lamOf q ρ₁) (a := a) (lam := 0) hLne hs2re this]
    have harg : (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I).im - (1 : ℂ).im) * L = 2 * mu := by
      have h1 : (((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I)).im = 2 * gam := by simp
      rw [h1, Complex.one_im, hmu]; ring
    rw [harg]
    simp
  -- ## the six bounds
  have hbU0 : Work.ZeroFreeTables.SigmaP3L q L χ₁ (sig : ℂ) a (Work.LinnikContract.lamOf q ρ₁)
      ≤ -(P3R 1 + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) mu)
        + (a + Work.LinnikContract.lamOf q ρ₁) * ((1/8 + ε/8) + ε/2) + (a + Work.LinnikContract.lamOf q ρ₁) * (ε/8) := by
    have hi := hLi (χ := χ₁) hχ1 (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁) hLile hlogqle
      hlam1nn hlam1lea (sig : ℂ) hs0re hs0im
    have hp := fmPointBound (χ₁.primitiveCharacter) hchi1 hprim ha hlam1nn hδ0 hδ1 hLt haδL
      hs0re hs0im (hlogOf (sig:ℂ) hs0re hs0im)
      (if (χ₁.primitiveCharacter).Even then 0 else 1) hpar0 hpar1
      (hCtp _ hparle (sig:ℂ) (by rw [hs0re]; linarith [div_pos ha hLpos])).1
      (hCtp _ hparle (sig:ℂ) (by rw [hs0re]; linarith [div_pos ha hLpos])).2
      (hJOf (sig:ℂ) hs0re hs0im) hminChi ({ρ₁, ρ₀} : Finset ℂ)
      (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h
          · rw [h]; exact hzr1
          · rw [h]; exact hzr0)
      (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h
          · rw [h]; exact himr1
          · rw [h]; exact himr0)
      (hEOf (sig:ℂ) hs0re hs0im ({ρ₁, ρ₀} : Finset ℂ) (by
        rw [Finset.card_insert_of_notMem (by simp [hne.symm]), Finset.card_singleton]
        try omega))
    rw [hT0s0] at hp
    exact le_trans hi (add_le_add hp (le_refl _))
  have hbV0 : Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) (sig : ℂ) a
        (Work.LinnikContract.lamOf q ρ₁) ≤ P3R ((a + Work.LinnikContract.lamOf q ρ₁) / a) + (a + Work.LinnikContract.lamOf q ρ₁) * (ε/8) := by
    have hp := hLp (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁) hLple hlogqle hlam1nn hlam1lea
      (sig : ℂ) hs0re hs0im
    rw [hP0] at hp
    exact hp
  have hbU1 : Work.ZeroFreeTables.SigmaP3L q L χ₁ ((sig : ℂ) + (gam : ℂ) * Complex.I) a
        (Work.LinnikContract.lamOf q ρ₁)
      ≤ -(Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₁) mu
          + P3R ((a + Work.LinnikContract.lamOf q ρ₁) / (a + Work.LinnikContract.lamOf q ρ₀))
          + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) (2 * mu))
        + (a + Work.LinnikContract.lamOf q ρ₁) * ((1/8 + ε/8) + ε/2) + (a + Work.LinnikContract.lamOf q ρ₁) * (ε/8) := by
    have hi := hLi (χ := χ₁) hχ1 (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁) hLile hlogqle
      hlam1nn hlam1lea ((sig : ℂ) + (gam : ℂ) * Complex.I) hs1re hs1im
    have hp := fmPointBound (χ₁.primitiveCharacter) hchi1 hprim ha hlam1nn hδ0 hδ1 hLt haδL
      hs1re hs1im (hlogOf _ hs1re hs1im)
      (if (χ₁.primitiveCharacter).Even then 0 else 1) hpar0 hpar1
      (hCtp _ hparle _ (by rw [hs1re]; linarith [div_pos ha hLpos])).1
      (hCtp _ hparle _ (by rw [hs1re]; linarith [div_pos ha hLpos])).2
      (hJOf _ hs1re hs1im) hminChi ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ)
      (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h | h
          · rw [h]; exact hzr1
          · rw [h]; exact hzr0
          · rw [h]; exact hzrc)
      (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h | h
          · rw [h]; exact himr1
          · rw [h]; exact himr0
          · rw [h]; exact himrc)
      (hEOf _ hs1re hs1im ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ) (by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hne.symm, hne1c⟩),
            Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hne0c),
            Finset.card_singleton]
        try omega))
    rw [hT1s1] at hp
    exact le_trans hi (add_le_add hp (le_refl _))
  have hbV1 : Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q)
        ((sig : ℂ) + (gam : ℂ) * Complex.I) a (Work.LinnikContract.lamOf q ρ₁)
      ≤ Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a mu + (a + Work.LinnikContract.lamOf q ρ₁) * (ε/8) := by
    have hp := hLp (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁) hLple hlogqle hlam1nn hlam1lea
      _ hs1re hs1im
    rw [hP1] at hp
    exact hp
  have hbU2 : Work.ZeroFreeTables.SigmaP3L q L χ₁ ((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I) a
        (Work.LinnikContract.lamOf q ρ₁)
      ≤ -(Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₁) (2 * mu)
          + Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) mu)
        + (a + Work.LinnikContract.lamOf q ρ₁) * ((1/8 + ε/8) + ε/2) + (a + Work.LinnikContract.lamOf q ρ₁) * (ε/8) := by
    have hi := hLi (χ := χ₁) hχ1 (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁) hLile hlogqle
      hlam1nn hlam1lea ((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I) hs2re hs2im
    have hp := fmPointBound (χ₁.primitiveCharacter) hchi1 hprim ha hlam1nn hδ0 hδ1 hLt haδL
      hs2re hs2im (hlogOf _ hs2re hs2im)
      (if (χ₁.primitiveCharacter).Even then 0 else 1) hpar0 hpar1
      (hCtp _ hparle _ (by rw [hs2re]; linarith [div_pos ha hLpos])).1
      (hCtp _ hparle _ (by rw [hs2re]; linarith [div_pos ha hLpos])).2
      (hJOf _ hs2re hs2im) hminChi ({ρ₁, ρ₀} : Finset ℂ)
      (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h
          · rw [h]; exact hzr1
          · rw [h]; exact hzr0)
      (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with h | h
          · rw [h]; exact himr1
          · rw [h]; exact himr0)
      (hEOf _ hs2re hs2im ({ρ₁, ρ₀} : Finset ℂ) (by
        rw [Finset.card_insert_of_notMem (by simp [hne.symm]), Finset.card_singleton]
        try omega))
    rw [hT0s2] at hp
    exact le_trans hi (add_le_add hp (le_refl _))
  have hbV2 : Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q)
        ((sig : ℂ) + ((2 * gam : ℝ) : ℂ) * Complex.I) a (Work.LinnikContract.lamOf q ρ₁)
      ≤ Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a (2 * mu) + (a + Work.LinnikContract.lamOf q ρ₁) * (ε/8) := by
    have hp := hLp (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁) hLple hlogqle hlam1nn hlam1lea
      _ hs2re hs2im
    rw [hP2] at hp
    exact hp
  -- ## the pointwise inequality
  have hsig1 : (1:ℝ) < sig := by rw [hsig]; linarith [div_pos ha hLpos]
  have h85 := Work.ZeroFreeTables.Table4.hb85 (γ := gam) χ₁ hsq (by linarith : (0:ℝ) ≤ K) hsig1 ha hlam1nn
  rw [← hLdef] at h85
  -- ## A and B brackets
  have hAnn : 0 ≤ (K ^ 2 + 1) * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) mu
      + 2 * K * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₁) mu
      - 2 * K * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a mu := by
    exact Work.ZeroFreeTables.Table4.A83_nonneg ha hlam1nn hlamle (by linarith) hcond
  have hBnn : 0 ≤ 2 * K * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₀) (2 * mu)
      + (1/2) * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) (a + Work.LinnikContract.lamOf q ρ₁) (2 * mu)
      - (1/2) * Work.ZeroFreeTables.Table4.P3AB (a + Work.LinnikContract.lamOf q ρ₁) a (2 * mu) := by
    exact Work.ZeroFreeTables.Table4.B83_nonneg ha hlam1nn hlamle hK hcond
  -- ## the final arithmetic
  have hselim : (a + Work.LinnikContract.lamOf q ρ₁) * (1/8 + 7 * ε / 8) ≤ (a + Work.LinnikContract.lamOf q ρ₁) * (1/8 + ε) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have hstep : 0 ≤ (K ^ 2 + 1/2) * (P3R ((a + Work.LinnikContract.lamOf q ρ₁) / a) - P3R 1) - 2 * K * P3R ((a + Work.LinnikContract.lamOf q ρ₁) / (a + Work.LinnikContract.lamOf q ρ₀))
      + (K + 1) ^ 2 * ((a + Work.LinnikContract.lamOf q ρ₁) * (1/8 + 7 * ε / 8)) := by
    have he : (a + Work.LinnikContract.lamOf q ρ₁) * ((1/8 + ε/8) + ε/2) + (a + Work.LinnikContract.lamOf q ρ₁) * (ε/8) + (a + Work.LinnikContract.lamOf q ρ₁) * (ε/8)
        = (a + Work.LinnikContract.lamOf q ρ₁) * (1/8 + 7 * ε / 8) := by ring
    have hKnn : (0:ℝ) ≤ K := by linarith
    -- combine h85 with the six bounds
    have h1 := mul_le_mul_of_nonneg_left hbV0 (by positivity : (0:ℝ) ≤ K^2 + 1/2)
    have h2 := mul_le_mul_of_nonneg_left hbU0 (by positivity : (0:ℝ) ≤ K^2 + 1/2)
    have h3 := mul_le_mul_of_nonneg_left hbV1 (by positivity : (0:ℝ) ≤ 2*K)
    have h4 := mul_le_mul_of_nonneg_left hbU1 (by positivity : (0:ℝ) ≤ 2*K)
    have h5 := mul_le_mul_of_nonneg_left hbV2 (by positivity : (0:ℝ) ≤ 1/2)
    have h6 := mul_le_mul_of_nonneg_left hbU2 (by positivity : (0:ℝ) ≤ 1/2)
    ring_nf at h85 h1 h2 h3 h4 h5 h6 hAnn hBnn ⊢
    linarith
  have hfin : 0 ≤ (K ^ 2 + 1/2) * (P3R ((a + Work.LinnikContract.lamOf q ρ₁) / a) - P3R 1) - 2 * K * P3R ((a + Work.LinnikContract.lamOf q ρ₁) / (a + Work.LinnikContract.lamOf q ρ₀))
      + (K + 1) ^ 2 * ((a + Work.LinnikContract.lamOf q ρ₁) * (1/8 + ε)) := by
    have hK1 : (0:ℝ) ≤ (K+1)^2 := by positivity
    have h7 := mul_le_mul_of_nonneg_left hselim hK1
    ring_nf at hstep h7 ⊢
    linarith
  -- conclude
  have hgoal : Work.ZeroFreeTables.p83 (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) a K
      = (K ^ 2 + 1/2) * (P3R ((a + Work.LinnikContract.lamOf q ρ₁) / a) - P3R 1)
        - 2 * K * P3R ((a + Work.LinnikContract.lamOf q ρ₁) / (a + Work.LinnikContract.lamOf q ρ₀))
        + (K + 1) ^ 2 * (a + Work.LinnikContract.lamOf q ρ₁) * (1/8) := rfl
  rw [hgoal, hal]
  ring_nf
  ring_nf at hfin
  linarith [hfin]

end Work.ZeroFreeTables.lam0w
