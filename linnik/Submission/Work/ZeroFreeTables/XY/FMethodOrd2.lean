import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs
import Submission.Work.ZeroFreeTables.XY.SupBoundOrd2
import Submission.Work.ZeroFreeTables.XY.KsumFiveNonneg
import Submission.Work.ZeroFreeTables.XY.KsumPrincipalComplex
import Submission.Work.ZeroFreeTables.XY.L52HypEighthDelta
import Submission.Work.ZeroFreeTables.XY.KsumTwoWorking
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Work.ZeroFreeTables.HBRepZeroStrict

/-!
# ZeroFreeTables — `XY/FMethodOrd2`

The order-2 (`χ₁² = 1`, `ρ₁` non-real) `F`-method inequality of Xylouris's §3.6,
i.e. HB (9.16) evaluated at `β = 1 - 1/𝓛` (`λ* = 1`) with HB Lemma 7.2's test
function at `λ = 4/3` (`xyT` of `XYDefs`):  `0 ≤ xyMain λ₁ + 240`.

## The reduction

Write `L = log q`, `β = 1 - 1/L`, `γ = ρ₁.im`, `λ₁ = λ(ρ₁)`, `f = xyT.f`.
HB (9.15)/(9.16) for the order-2 case is the five-term `K`-sum inequality

  `0 ≤ 14379·K(β,1) + 24480·K(β+iγ,χ₁) + 14900·K(β+2iγ,1) + 6000·K(β+3iγ,χ₁) + 1250·K(β+4iγ,1)`

(`KsumFiveNonneg`, from the Chebyshev identity `(3+10c cos θ)²(9+10c cos θ)²`).  The five terms
are bounded by

* principal character: `Ksum_principal_le` (at `β`, giving `L·xyF(-1)`) and
  `KsumPrincipalComplex` (at `β+2iγ`, `β+4iγ`, giving `L·xyRe(-1)(2γL)`, `L·xyRe(-1)(4γL)`),
  each with error `f(0)εL`;
* `χ₁`: the working form of HB Lemma 5.2 (`KsumTwoWorking`, Xylouris's Lemma 3.4) at
  `s = β+iγ` and `s = β+3iγ`, retaining the two zeros `ρ₁`, `ρ̄₁` (the only zeros to the right
  of `s`, by the isolation hypothesis) — giving `-L·(F(λ₁-1) + xyRe(λ₁-1)(2γL))` and
  `-L·(xyRe(λ₁-1)(2γL) + xyRe(λ₁-1)(4γL))` with error `f(0)(1/8+ε)L`.

Summing gives `0 ≤ L·(xyMain λ₁ + xySup1 λ₁ (2γL) + xySup2 λ₁ (4γL)) + L·f(0)·61009·ε`, and with
`ε = 1/10000` (`61009·(64/45)/10⁴ ≈ 8.68 ≤ 20`) and `SupBoundOrd2`
(`xySup1 ≤ 60`, `xySup2 ≤ 160`) this is `0 ≤ xyMain λ₁ + 240`.

The case `2 ≤ zeroMult χ₁ ρ₁` (Xylouris's *Fall 1*) is excluded by the repeated-zero bound
`HBRepZeroStrict` (`λ₁ > 696/1000`), so in the derivation both retained zeros are simple.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 2000000

namespace Work.ZeroFreeTables.XY

/-! ## Bridges between the complex Laplace transform and `xyF`/`xyRe` -/

/-- `xyRe` is the real part of `Fc` at `z.re + i z.im`. -/
theorem fmo2_Fc_re_eq (z : ℂ) : (xyT.Fc z).re = xyRe z.re z.im := by
  rw [xyRe]
  exact (congrArg Complex.re (congrArg xyT.Fc (Complex.re_add_im z))).symm

/-- The defining integral of `Fc`, with real part taken, as an `xyRe`-value. -/
theorem fmo2_integral_re (z : ℂ) :
    (∫ t in (0:ℝ)..xyT.x₀, Complex.exp (-(z * (t : ℂ))) * ((xyT.f t : ℝ) : ℂ)).re
      = xyRe z.re z.im := by
  rw [← xyT.Fc_spec z, fmo2_Fc_re_eq]

/-- On the real axis `xyRe` is `xyF`. -/
theorem xyRe_zero_right (x : ℝ) : xyRe x 0 = xyF x := by
  simp only [xyRe, xyF, TestFn.F, Complex.ofReal_zero, zero_mul, add_zero]

/-- Real part of `(s - ρ) * L` for real `L`. -/
theorem fmo2_mul_re (s ρ : ℂ) (L : ℝ) : ((s - ρ) * ((L : ℝ) : ℂ)).re = (s.re - ρ.re) * L := by
  simp [Complex.mul_re, Complex.sub_re]

/-- Imaginary part of `(s - ρ) * L` for real `L`. -/
theorem fmo2_mul_im (s ρ : ℂ) (L : ℝ) : ((s - ρ) * ((L : ℝ) : ℂ)).im = (s.im - ρ.im) * L := by
  simp [Complex.mul_im, Complex.sub_im]

/-- The `K`-sum as a `tsum`, in the exact shape produced by the consumers. -/
theorem Kxy_eq_tsum (q : ℕ) [NeZero q] (f : ℝ → ℝ) (L β t : ℝ) (χ : DirichletCharacter ℂ q) :
    Kxy f L β t χ = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I)).re) *
        f (Real.log n / L) := rfl

/-- The `K`-sum at `t = 0` for the principal character, in the shape of HB (6.9). -/
theorem Kxy0_eq_tsum_flat (q : ℕ) [NeZero q] (f : ℝ → ℝ) (L β : ℝ) :
    Kxy0 q f L β 0 = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      (((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re) *
        f (Real.log n / L) := by
  unfold Kxy0
  refine tsum_congr fun n => ?_
  simp only [Complex.ofReal_zero, zero_mul, add_zero]

/-- `Kxy0` as a `tsum`, in the exact shape produced by the consumers. -/
theorem Kxy0_eq_tsum' {q : ℕ} [NeZero q] (f : ℝ → ℝ) (L β t : ℝ) :
    Kxy0 q f L β t = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      (((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I)).re) *
        f (Real.log n / L) := rfl

/-- `xyF (-1)` is the integral appearing in the paper's principal-character bound. -/
theorem xyF_neg_one_eq :
    xyF (-1) = ∫ t in (0:ℝ)..xyT.x₀, Real.exp (1 * t) * xyT.f t := by
  rw [xyF_eq_integral, xyT_x0]
  exact intervalIntegral.integral_congr (fun u _ => by ring_nf)

/-- `xyRe (-1) v` is the integral appearing in the paper's principal-character bound. -/
theorem xyRe_neg_one_eq (v : ℝ) :
    xyRe (-1) v = ∫ t in (0:ℝ)..xyT.x₀,
      Real.cos (v * t) * (Real.exp (-((-1) * t)) * xyT.f t) := by
  rw [xyRe_eq_integral, xyT_x0]

theorem FMethodOrd2 : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
    Work.LinnikContract.lamOf q ρ₁ ≤ 628/1000 → 518/1000 ≤ Work.LinnikContract.lamOf q ρ₁ →
    (∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 4 → u ≠ ρ₁ →
      u ≠ starRingEnd ℂ ρ₁ → 1 ≤ Work.LinnikContract.lamOf q u) →
    0 ≤ Work.ZeroFreeTables.xyMain (Work.LinnikContract.lamOf q ρ₁) + 240 := by
  -- ===== providers =====
  obtain ⟨B, hB0, hBnd⟩ := xyT.f_bound
  obtain ⟨qP, hP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le xyT.x₀ B xyT.x₀_pos hB0
    xyT.f_cont xyT.f_supp xyT.f_diff hBnd (ε := 1 / 10000) (by norm_num) xyT.f0_pos
  obtain ⟨qC, hC⟩ := KsumPrincipalComplex xyT.x₀ B xyT.x₀_pos hB0
    xyT.f_cont xyT.f_supp xyT.f_diff hBnd (ε := 1 / 10000) (by norm_num) xyT.f0_pos
  obtain ⟨δ, hδ0, hδ1, qL, hL52⟩ := L52HypEighth_fixedDelta
  obtain ⟨qW, hW⟩ := KsumTwoWorking xyT.x₀ B (1/8) xyT.x₀_pos hB0
    (f := xyT.f) xyT.f_cont xyT.f_supp xyT.f_diff hBnd xyT.f0_pos
    (fun z hz => by rw [← xyT.Fc_spec z]; exact xyT.Fc_re_nonneg z hz)
    (ε := 1 / 10000) (by norm_num) hδ0 hδ1
  obtain ⟨qR, hR⟩ := HBRepZeroStrict
  refine ⟨max (max (max (max (max qP qC) qL) qW) qR) (10 ^ 7), ?_⟩
  intro q hq hqne χ₁ ρ₁ hmw hsq him hlam_hi hlam_lo hsep
  haveI : NeZero q := hqne
  simp only [max_le_iff] at hq
  have hqP : qP ≤ q := by omega
  have hqC : qC ≤ q := by omega
  have hqL : qL ≤ q := by omega
  have hqW : qW ≤ q := by omega
  have hqR : qR ≤ q := by omega
  have hqbig : 10 ^ 7 ≤ q := by omega
  have hchi1ne : χ₁ ≠ 1 := hmw.1.1.1
  have hzm : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmw.1.1.2.1
  have hgabs1 : |ρ₁.im| ≤ 1 := hmw.1.1.2.2
  have hsq' : χ₁ * χ₁ = 1 := by rw [← pow_two]; exact hsq
  haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  -- ===== the multiplicity case (Xylouris's Fall 1) is impossible =====
  have hsimple : Work.LinnikContract.zeroMult χ₁ ρ₁ = 1 := by
    by_contra hne
    have hm2 : 2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ := by omega
    have hnr : ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) := fun h => him h.2
    have hgt := hR q hqR χ₁ ρ₁ hmw hnr hm2
    linarith
  -- ===== setup =====
  set L : ℝ := Real.log (q : ℝ) with hLdef
  set β : ℝ := 1 - 1 / L with hbetaDef
  set γ : ℝ := ρ₁.im with hgammaDef
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos hq1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hL6 : 6 ≤ L := by
    rw [hLdef]
    have h1000 : (1000 : ℝ) ≤ q := by exact_mod_cast (by omega : 1000 ≤ q)
    have h1 : Real.log 1000 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) h1000
    have h2 : (6 : ℝ) ≤ Real.log 1000 := by
      rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]
      have hexp2 : Real.exp 2 ≤ 10 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
      have hlog10 : 2 ≤ Real.log 10 := (Real.le_log_iff_exp_le (by norm_num)).mpr hexp2
      push_cast
      nlinarith
    linarith
  have hlogL1 : 1 ≤ Real.log L := by
    have he : Real.exp 1 < L := lt_of_lt_of_le Real.exp_one_lt_three (by linarith)
    exact (Real.le_log_iff_exp_le hLpos).mpr he.le
  have hsqrtlog : 1 ≤ Real.sqrt (Real.log L) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hlamEq : ∀ u : ℂ, Work.LinnikContract.lamOf q u = (1 - u.re) * L := by
    intro u; rw [Work.LinnikContract.lamOf, ← hLdef]
  have hlam1pos : 0 < Work.LinnikContract.lamOf q ρ₁ := by
    have h1 : (518:ℝ)/1000 ≤ (1 - ρ₁.re) * L := by rw [← hlamEq ρ₁]; exact hlam_lo
    nlinarith [hLpos]
  have hrre_lt : ρ₁.re < 1 := by
    have h1 : 0 < (1 - ρ₁.re) * L := by rw [← hlamEq ρ₁]; exact hlam1pos
    nlinarith [hLpos]
  have hrre_pos : 0 < ρ₁.re := by
    have h1 : (1 - ρ₁.re) * L ≤ 628/1000 := by rw [← hlamEq ρ₁]; exact hlam_hi
    have h2 : (0:ℝ) ≤ 1 - ρ₁.re := by linarith [hrre_lt]
    nlinarith [h1, h2, hL6]
  have hgabs : |γ| ≤ 1 := by rw [hgammaDef]; exact hgabs1
  have hgne : γ ≠ 0 := by rw [hgammaDef]; exact him
  have hnorm : ‖ρ₁‖ ≤ |γ| + 2 := by
    have h2 : ρ₁.im = γ := hgammaDef.symm
    have h3 : ρ₁.re ^ 2 ≤ 1 := by nlinarith [hrre_pos, hrre_lt]
    have h1 : ‖ρ₁‖ ^ 2 ≤ (|γ| + 2) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, h2]
      nlinarith [sq_nonneg γ, abs_nonneg γ, h3, sq_abs γ]
    have h4 : 0 ≤ ‖ρ₁‖ := norm_nonneg _
    have h5 : 0 ≤ |γ| + 2 := by positivity
    by_contra hcon
    push Not at hcon
    have h6 : (|γ| + 2) ^ 2 < ‖ρ₁‖ ^ 2 := by nlinarith [hcon, h4, h5]
    linarith [h1]
  have hnormc : ‖((starRingEnd ℂ) ρ₁)‖ ≤ |γ| + 2 := by simpa using hnorm
  -- ===== the primitive character, analyticity, divisor values =====
  have hprim_ne : χ₁.primitiveCharacter ≠ 1 := by
    intro h
    refine hchi1ne ?_
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h]
    exact DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level
  have hanal : ∀ R : ℝ, AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 R) :=
    fun R z _ => (DirichletCharacter.differentiable_completedLFunction hprim_ne).analyticAt z
  have hordEq : ∀ R : ℝ, ρ₁ ∈ Metric.closedBall 0 R →
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 R)) ρ₁ : ℤ) : ℝ) = 1 := by
    intro R hR
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hanal R) hR]
    have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) ρ₁
        = 1 := by
      simpa only [Work.LinnikContract.zeroMult] using hsimple
    rw [h1]; norm_num
  have hordEqc : ∀ R : ℝ, ((starRingEnd ℂ) ρ₁) ∈ Metric.closedBall 0 R →
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 R)) ((starRingEnd ℂ) ρ₁) : ℤ) : ℝ) = 1 := by
    intro R hR
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hanal R) hR]
    have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (starRingEnd ℂ ρ₁) = 1 := by
      have h2 : Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) = 1 := by
        rw [Work.A7.zeroMult_conj_sq_one χ₁ hsq ρ₁]; exact hsimple
      simpa only [Work.LinnikContract.zeroMult] using h2
    rw [h1]; norm_num
  -- ===== region conditions =====
  have hsre : ∀ c : ℝ, (((β : ℂ) + (c : ℂ) * Complex.I)).re = β := by
    intro c
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have hsim : ∀ c : ℝ, (((β : ℂ) + (c : ℂ) * Complex.I)).im = c := by
    intro c
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, add_zero]
  have hsig1 : |β - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [← hLdef]
    have h1 : |β - 1| = 1 / L := by
      rw [hbetaDef,
        show (1:ℝ) - 1 / L - 1 = -(1 / L) by ring, abs_neg, abs_of_nonneg (by positivity)]
    rw [h1]
    exact div_le_div_of_nonneg_right hsqrtlog hLpos.le
  have hsig2 : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ β := by
    rw [← hLdef]
    have h3 : 1 / L ≤ Real.sqrt (Real.log L) / L := div_le_div_of_nonneg_right hsqrtlog hLpos.le
    rw [hbetaDef]; linarith
  -- ===== the "only zeros to the right in the window" hypothesis =====
  have honly_gen : ∀ t : ℝ, |t| ≤ 3 → ∀ u : ℂ,
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 (|(((β : ℂ) + (t : ℂ) * Complex.I)).im| + 2))) u ≠ 0 →
      ‖(1 : ℂ) + ((((β : ℂ) + (t : ℂ) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ →
      (((β : ℂ) + (t : ℂ) * Complex.I)).re < u.re →
        u = ρ₁ ∨ u = ((starRingEnd ℂ) ρ₁) := by
    intro t ht u hdu hwin hgt
    by_cases hone : u = ρ₁
    · exact Or.inl hone
    by_cases hone' : u = ((starRingEnd ℂ) ρ₁)
    · exact Or.inr hone'
    exfalso
    have hmem : u ∈ Metric.closedBall 0 (|(((β : ℂ) + (t : ℂ) * Complex.I)).im| + 2) := by
      by_contra hnot
      refine hdu ?_
      have hnot' : ¬ (MeromorphicOn (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 (|(((β : ℂ) + (t : ℂ) * Complex.I)).im| + 2))
          ∧ u ∈ Metric.closedBall 0 (|(((β : ℂ) + (t : ℂ) * Complex.I)).im| + 2)) :=
        fun h => hnot h.2
      rw [MeromorphicOn.divisor_def, if_neg hnot']
    have hzn : Work.LinnikContract.zeroMult χ₁ u ≠ 0 := by
      have hcast : ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          u : ℕ) : ℤ) ≠ 0 := by
        rw [← Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hanal _) hmem]
        exact hdu
      have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) u
          ≠ 0 := fun h0 => hcast (by rw [h0]; rfl)
      simpa only [Work.LinnikContract.zeroMult] using hnat
    have himu : |u.im| ≤ 4 := by
      have h1 : |t - u.im| ≤ δ := by
        have h2 : |((1 : ℂ) + ((((β : ℂ) + (t : ℂ) * Complex.I)).im : ℂ) * Complex.I - u).im|
            ≤ δ :=
          le_trans (Complex.abs_im_le_norm _) hwin
        rw [hsim t] at h2
        simpa using h2
      have h3 : |u.im| ≤ |t| + |t - u.im| := by
        calc |u.im| = |t - (t - u.im)| := by ring_nf
          _ ≤ |t| + |t - u.im| := abs_sub _ _
      linarith [ht, hδ1]
    have hsep' : 1 ≤ Work.LinnikContract.lamOf q u := hsep u hzn himu hone hone'
    have hkey : (1 : ℝ) / L ≤ 1 - u.re := by
      rw [div_le_iff₀ hLpos, ← hlamEq u]
      exact hsep'
    have hgt' : β < u.re := by rwa [hsre t] at hgt
    rw [hbetaDef] at hgt'
    linarith
  -- ===== divisor values in ℤ-shape, and the two principal bounds =====
  have hordZ : ∀ R : ℝ, ρ₁ ∈ Metric.closedBall 0 R →
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 R) ρ₁ = 1 := by
    intro R hR
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hanal R) hR]
    have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) ρ₁
        = 1 := by simpa only [Work.LinnikContract.zeroMult] using hsimple
    rw [h1]; norm_num
  have hordZc : ∀ R : ℝ, ((starRingEnd ℂ) ρ₁) ∈ Metric.closedBall 0 R →
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 R) ((starRingEnd ℂ) ρ₁) = 1 := by
    intro R hR
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hanal R) hR]
    have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (starRingEnd ℂ ρ₁) = 1 := by
      have h2 : Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) = 1 := by
        rw [Work.A7.zeroMult_conj_sq_one χ₁ hsq ρ₁]; exact hsimple
      simpa only [Work.LinnikContract.zeroMult] using h2
    rw [h1]; norm_num
  have b1 : Kxy0 q xyT.f L β 0 ≤ L * xyF (-1) + xyT.f 0 * (1 / 10000) * L := by
    have h := hP hqP (β := β) (lam := 1) (by rw [hbetaDef, ← hLdef]; field_simp; ring) hsig1
    rw [Kxy0_eq_tsum_flat]
    rw [← hLdef] at h
    rw [← xyF_neg_one_eq] at h
    linarith
  have htau2 : |2 * γ| ≤ Real.log (q : ℝ) := by
    rw [← hLdef]
    have h2 : |2 * γ| = 2 * |γ| := by rw [abs_mul]; norm_num
    rw [h2]; linarith [hgabs, hL6]
  have htau4 : |4 * γ| ≤ Real.log (q : ℝ) := by
    rw [← hLdef]
    have h2 : |4 * γ| = 4 * |γ| := by rw [abs_mul]; norm_num
    rw [h2]; linarith [hgabs, hL6]
  have hIntI : ∀ v : ℝ, (∫ t in (0:ℝ)..xyT.x₀,
        Real.cos (v * Real.log (q : ℝ) * t) *
          (Real.exp (-((β - 1) * Real.log (q : ℝ) * t)) * xyT.f t)) = xyRe (-1) (v * L) := by
    intro v
    rw [xyRe_neg_one_eq, ← hLdef]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    have hexp : (β - 1) * L = -1 := by rw [hbetaDef]; field_simp; ring
    rw [hexp]
  have b3 : Kxy0 q xyT.f L β (2 * γ) ≤
      L * xyRe (-1) (2 * γ * L) + xyT.f 0 * (1 / 10000) * L := by
    have h := hC hqC (σ := β) (τ := 2 * γ) hsig1 htau2
    rw [Kxy0_eq_tsum']
    rw [← hLdef] at h
    rw [hIntI (2 * γ)] at h
    linarith
  have b5 : Kxy0 q xyT.f L β (4 * γ) ≤
      L * xyRe (-1) (4 * γ * L) + xyT.f 0 * (1 / 10000) * L := by
    have h := hC hqC (σ := β) (τ := 4 * γ) hsig1 htau4
    rw [Kxy0_eq_tsum']
    rw [← hLdef] at h
    rw [hIntI (4 * γ)] at h
    linarith
  -- ===== common facts for the two χ₁-bounds =====
  have hlamlt1 : Work.LinnikContract.lamOf q ρ₁ < 1 := lt_of_le_of_lt hlam_hi (by norm_num)
  have hbeta_lt : β < ρ₁.re := by
    rw [hbetaDef]
    have h3 : 1 - ρ₁.re < 1 / L := by
      rw [lt_div_iff₀ hLpos, ← hlamEq ρ₁]
      exact hlamlt1
    linarith
  have hzreL : ∀ ρ : ℂ, (((((β : ℂ) + (γ : ℂ) * Complex.I) - ρ) * ((L : ℝ) : ℂ))).re
      = (1 - ρ.re) * L - 1 := by
    intro ρ
    rw [fmo2_mul_re, hsre γ, hbetaDef]
    field_simp
    ring
  have hzabs : |(1 - ρ₁.re) * L - 1| ≤ 1 := by
    have h1 : (1 - ρ₁.re) * L = Work.LinnikContract.lamOf q ρ₁ := (hlamEq ρ₁).symm
    rw [h1, abs_le]
    constructor <;> linarith [hlam_lo, hlam_hi]
  have hH : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/8) (1/10000/2) δ :=
    hL52 q hqL χ₁ hchi1ne hsq' (1/10000/2) (by norm_num) (by norm_num)
  -- ===== b2: the χ₁-sum at s = β + iγ =====
  have b2 : Kxy xyT.f L β γ χ₁ ≤
      -(L * xyF (Work.LinnikContract.lamOf q ρ₁ - 1))
        - L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L)
        + xyT.f 0 * (1/8 + 1/10000) * L := by
    set z1 : ℂ := (((β : ℂ) + (γ : ℂ) * Complex.I) - ρ₁) * ((L : ℝ) : ℂ) with hz1
    set z2 : ℂ :=
      (((β : ℂ) + (γ : ℂ) * Complex.I) - ((starRingEnd ℂ) ρ₁)) * ((L : ℝ) : ℂ) with hz2
    have hz1re : z1.re = Work.LinnikContract.lamOf q ρ₁ - 1 := by
      rw [hz1, hzreL ρ₁, ← hlamEq ρ₁]
    have hz1im : z1.im = 0 := by
      rw [hz1, fmo2_mul_im, hsim γ, hgammaDef]; ring
    have hz2re : z2.re = Work.LinnikContract.lamOf q ρ₁ - 1 := by
      rw [hz2, hzreL ((starRingEnd ℂ) ρ₁),
        show ((starRingEnd ℂ) ρ₁).re = ρ₁.re from Complex.conj_re ρ₁, ← hlamEq ρ₁]
    have hz2im : z2.im = 2 * γ * L := by
      rw [hz2, fmo2_mul_im, hsim γ, Complex.conj_im, hgammaDef]; ring
    have hInt1 : (∫ t in (0:ℝ)..xyT.x₀,
        Complex.exp (-(z1 * (t : ℂ))) * ((xyT.f t : ℝ) : ℂ)).re
          = xyF (Work.LinnikContract.lamOf q ρ₁ - 1) := by
      rw [fmo2_integral_re, hz1re, hz1im, xyRe_zero_right]
    have hInt2 : (∫ t in (0:ℝ)..xyT.x₀,
        Complex.exp (-(z2 * (t : ℂ))) * ((xyT.f t : ℝ) : ℂ)).re
          = xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L) := by
      rw [fmo2_integral_re, hz2re, hz2im]
    have hball : ρ₁ ∈ Metric.closedBall 0 (|(((β : ℂ) + (γ : ℂ) * Complex.I)).im| + 2) := by
      rw [hsim γ, Metric.mem_closedBall, dist_zero_right]
      linarith [hnorm]
    have hballc : ((starRingEnd ℂ) ρ₁) ∈
        Metric.closedBall 0 (|(((β : ℂ) + (γ : ℂ) * Complex.I)).im| + 2) := by
      rw [hsim γ, Metric.mem_closedBall, dist_zero_right]
      linarith [hnormc]
    have hreg1 : |(((β : ℂ) + (γ : ℂ) * Complex.I)).re - 1|
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
      rw [hsre γ]; exact hsig1
    have hreg2 : |(((β : ℂ) + (γ : ℂ) * Complex.I)).im| ≤ 10 * Real.log (q : ℝ) := by
      rw [hsim γ, ← hLdef]; linarith [hgabs, hL6]
    have hreg3 : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ)
        ≤ (((β : ℂ) + (γ : ℂ) * Complex.I)).re := by
      rw [hsre γ]; exact hsig2
    have hd1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + (γ : ℂ) * Complex.I)).im| + 2))) ρ₁ ≠ 0 := by
      rw [hordZ _ hball]; norm_num
    have hd2 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + (γ : ℂ) * Complex.I)).im| + 2)))
          ((starRingEnd ℂ) ρ₁) ≠ 0 := by
      rw [hordZc _ hballc]; norm_num
    have hm1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + (γ : ℂ) * Complex.I)).im| + 2))) ρ₁ ≤ 10 := by
      rw [hordZ _ hball]; norm_num
    have hm2 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + (γ : ℂ) * Complex.I)).im| + 2)))
          ((starRingEnd ℂ) ρ₁) ≤ 10 := by
      rw [hordZc _ hballc]; norm_num
    have hne : ρ₁ ≠ ((starRingEnd ℂ) ρ₁) := by
      intro hcon
      exact hgne (by rw [hgammaDef]; exact Complex.conj_eq_iff_im.mp hcon.symm)
    have hlt1 : (((β : ℂ) + (γ : ℂ) * Complex.I)).re < ρ₁.re := by
      rw [hsre γ]; exact hbeta_lt
    have hlt2 : (((β : ℂ) + (γ : ℂ) * Complex.I)).re < ((starRingEnd ℂ) ρ₁).re := by
      rw [hsre γ, Complex.conj_re]; exact hbeta_lt
    have hzr1 : |((((β : ℂ) + (γ : ℂ) * Complex.I) - ρ₁)
        * ((Real.log (q : ℝ) : ℝ) : ℂ)).re| ≤ 1 := by
      rw [← hLdef, ← hz1, hz1re, hlamEq ρ₁]
      exact hzabs
    have hzr2 : |((((β : ℂ) + (γ : ℂ) * Complex.I) - ((starRingEnd ℂ) ρ₁))
        * ((Real.log (q : ℝ) : ℝ) : ℂ)).re| ≤ 1 := by
      rw [← hLdef, ← hz2, hz2re, hlamEq ρ₁]
      exact hzabs
    have honly := honly_gen γ (by linarith [hgabs] : |γ| ≤ 3)
    have h := hW hqW χ₁ hchi1ne (s := (β : ℂ) + (γ : ℂ) * Complex.I)
      (ρ := ρ₁) (ρ' := starRingEnd ℂ ρ₁)
      hreg1 hreg2 hreg3 hH hd1 hd2 hne hlt1 hlt2 hm1 hm2 hzr1 hzr2 honly
    rw [← hLdef] at h
    rw [← Kxy_eq_tsum] at h
    rw [← hz1, ← hz2] at h
    rw [hordEq _ hball, hInt1, hordEqc _ hballc, hInt2] at h
    linarith [h]
  -- ===== b4: the χ₁-sum at s = β + 3iγ =====
  have b4 : Kxy xyT.f L β (3 * γ) χ₁ ≤
      -(L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L))
        - L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (4 * γ * L)
        + xyT.f 0 * (1/8 + 1/10000) * L := by
    have hb4 : |3 * γ| = 3 * |γ| := by rw [abs_mul]; norm_num
    have hs3 : (((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).re = β := hsre (3 * γ)
    have hi3 : (((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).im = 3 * γ := hsim (3 * γ)
    have hzreL3 : ∀ ρ : ℂ, (((((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I) - ρ)
        * ((L : ℝ) : ℂ))).re = (1 - ρ.re) * L - 1 := by
      intro ρ
      rw [fmo2_mul_re, hs3, hbetaDef]
      field_simp
      ring
    set z1 : ℂ := (((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I) - ρ₁) * ((L : ℝ) : ℂ) with hz1
    set z2 : ℂ :=
      (((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I) - ((starRingEnd ℂ) ρ₁)) * ((L : ℝ) : ℂ)
        with hz2
    have hz1re : z1.re = Work.LinnikContract.lamOf q ρ₁ - 1 := by
      rw [hz1, hzreL3 ρ₁, ← hlamEq ρ₁]
    have hz1im : z1.im = 2 * γ * L := by
      rw [hz1, fmo2_mul_im, hi3, hgammaDef]; ring
    have hz2re : z2.re = Work.LinnikContract.lamOf q ρ₁ - 1 := by
      rw [hz2, hzreL3 ((starRingEnd ℂ) ρ₁),
        show ((starRingEnd ℂ) ρ₁).re = ρ₁.re from Complex.conj_re ρ₁, ← hlamEq ρ₁]
    have hz2im : z2.im = 4 * γ * L := by
      rw [hz2, fmo2_mul_im, hi3, Complex.conj_im, hgammaDef]; ring
    have hInt1 : (∫ t in (0:ℝ)..xyT.x₀,
        Complex.exp (-(z1 * (t : ℂ))) * ((xyT.f t : ℝ) : ℂ)).re
          = xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L) := by
      rw [fmo2_integral_re, hz1re, hz1im]
    have hInt2 : (∫ t in (0:ℝ)..xyT.x₀,
        Complex.exp (-(z2 * (t : ℂ))) * ((xyT.f t : ℝ) : ℂ)).re
          = xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (4 * γ * L) := by
      rw [fmo2_integral_re, hz2re, hz2im]
    have hball : ρ₁ ∈ Metric.closedBall 0 (|(((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).im| + 2) := by
      rw [hi3, Metric.mem_closedBall, dist_zero_right, hb4]
      linarith [hnorm, abs_nonneg γ]
    have hballc : ((starRingEnd ℂ) ρ₁) ∈
        Metric.closedBall 0 (|(((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).im| + 2) := by
      rw [hi3, Metric.mem_closedBall, dist_zero_right, hb4]
      linarith [hnormc, abs_nonneg γ]
    have hreg1 : |(((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).re - 1|
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
      rw [hs3]; exact hsig1
    have hreg2 : |(((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).im| ≤ 10 * Real.log (q : ℝ) := by
      rw [hi3, hb4, ← hLdef]; linarith [hgabs, hL6]
    have hreg3 : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ)
        ≤ (((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).re := by
      rw [hs3]; exact hsig2
    have hd1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).im| + 2))) ρ₁
          ≠ 0 := by
      rw [hordZ _ hball]; norm_num
    have hd2 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).im| + 2)))
          ((starRingEnd ℂ) ρ₁) ≠ 0 := by
      rw [hordZc _ hballc]; norm_num
    have hm1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).im| + 2))) ρ₁
          ≤ 10 := by
      rw [hordZ _ hball]; norm_num
    have hm2 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).im| + 2)))
          ((starRingEnd ℂ) ρ₁) ≤ 10 := by
      rw [hordZc _ hballc]; norm_num
    have hne : ρ₁ ≠ ((starRingEnd ℂ) ρ₁) := by
      intro hcon
      exact hgne (by rw [hgammaDef]; exact Complex.conj_eq_iff_im.mp hcon.symm)
    have hlt1 : (((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).re < ρ₁.re := by
      rw [hs3]; exact hbeta_lt
    have hlt2 : (((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).re < ((starRingEnd ℂ) ρ₁).re := by
      rw [hs3, Complex.conj_re]; exact hbeta_lt
    have hzr1 : |((((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I) - ρ₁)
        * ((Real.log (q : ℝ) : ℝ) : ℂ)).re| ≤ 1 := by
      rw [← hLdef, ← hz1, hz1re, hlamEq ρ₁]
      exact hzabs
    have hzr2 : |((((β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I) - ((starRingEnd ℂ) ρ₁))
        * ((Real.log (q : ℝ) : ℝ) : ℂ)).re| ≤ 1 := by
      rw [← hLdef, ← hz2, hz2re, hlamEq ρ₁]
      exact hzabs
    have honly := honly_gen (3 * γ) (by rw [hb4]; linarith [hgabs])
    have h := hW hqW χ₁ hchi1ne (s := (β : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)
      (ρ := ρ₁) (ρ' := starRingEnd ℂ ρ₁)
      hreg1 hreg2 hreg3 hH hd1 hd2 hne hlt1 hlt2 hm1 hm2 hzr1 hzr2 honly
    rw [← hLdef] at h
    rw [← Kxy_eq_tsum] at h
    rw [← hz1, ← hz2] at h
    rw [hordEq _ hball, hInt1, hordEqc _ hballc, hInt2] at h
    linarith [h]
  -- ===== the five-term combination =====
  have hpos := KsumFiveNonneg (q := q) (f := xyT.f) (fun t => xyT.f_nonneg t) (x₀ := xyT.x₀)
    (L := L) (β := β) (γ := γ) xyT.x₀_pos hLpos xyT.f_supp χ₁ hsq
  simp only [Kxy_one_eq_Kxy0] at hpos
  have h1 := mul_le_mul_of_nonneg_left b1 (by norm_num : (0:ℝ) ≤ 14379)
  have h2 := mul_le_mul_of_nonneg_left b2 (by norm_num : (0:ℝ) ≤ 24480)
  have h3 := mul_le_mul_of_nonneg_left b3 (by norm_num : (0:ℝ) ≤ 14900)
  have h4 := mul_le_mul_of_nonneg_left b4 (by norm_num : (0:ℝ) ≤ 6000)
  have h5 := mul_le_mul_of_nonneg_left b5 (by norm_num : (0:ℝ) ≤ 1250)
  have hid : 14379 * (L * xyF (-1) + xyT.f 0 * (1 / 10000) * L)
      + 24480 * (-(L * xyF (Work.LinnikContract.lamOf q ρ₁ - 1))
          - L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L)
          + xyT.f 0 * (1/8 + 1/10000) * L)
      + 14900 * (L * xyRe (-1) (2 * γ * L) + xyT.f 0 * (1 / 10000) * L)
      + 6000 * (-(L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L))
          - L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (4 * γ * L)
          + xyT.f 0 * (1/8 + 1/10000) * L)
      + 1250 * (L * xyRe (-1) (4 * γ * L) + xyT.f 0 * (1 / 10000) * L)
    = L * (xyMain (Work.LinnikContract.lamOf q ρ₁)
        + xySup1 (Work.LinnikContract.lamOf q ρ₁) (2 * γ * L)
        + xySup2 (Work.LinnikContract.lamOf q ρ₁) (4 * γ * L))
      + L * (xyT.f 0 * 61009 * (1 / 10000)) := by
    simp only [xyMain, xySup1, xySup2]
    ring
  have hsum : 14379 * Kxy0 q xyT.f L β 0 + 24480 * Kxy xyT.f L β γ χ₁
      + 14900 * Kxy0 q xyT.f L β (2 * γ) + 6000 * Kxy xyT.f L β (3 * γ) χ₁
      + 1250 * Kxy0 q xyT.f L β (4 * γ)
      ≤ 14379 * (L * xyF (-1) + xyT.f 0 * (1 / 10000) * L)
      + 24480 * (-(L * xyF (Work.LinnikContract.lamOf q ρ₁ - 1))
          - L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L)
          + xyT.f 0 * (1/8 + 1/10000) * L)
      + 14900 * (L * xyRe (-1) (2 * γ * L) + xyT.f 0 * (1 / 10000) * L)
      + 6000 * (-(L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L))
          - L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (4 * γ * L)
          + xyT.f 0 * (1/8 + 1/10000) * L)
      + 1250 * (L * xyRe (-1) (4 * γ * L) + xyT.f 0 * (1 / 10000) * L) := by
    linarith [h1, h2, h3, h4, h5]
  have hcomb : 0 ≤ L * (xyMain (Work.LinnikContract.lamOf q ρ₁)
        + xySup1 (Work.LinnikContract.lamOf q ρ₁) (2 * γ * L)
        + xySup2 (Work.LinnikContract.lamOf q ρ₁) (4 * γ * L))
      + L * (xyT.f 0 * 61009 * (1 / 10000)) := by
    have h0 : 0 ≤ 14379 * (L * xyF (-1) + xyT.f 0 * (1 / 10000) * L)
        + 24480 * (-(L * xyF (Work.LinnikContract.lamOf q ρ₁ - 1))
            - L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L)
            + xyT.f 0 * (1/8 + 1/10000) * L)
        + 14900 * (L * xyRe (-1) (2 * γ * L) + xyT.f 0 * (1 / 10000) * L)
        + 6000 * (-(L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (2 * γ * L))
            - L * xyRe (Work.LinnikContract.lamOf q ρ₁ - 1) (4 * γ * L)
            + xyT.f 0 * (1/8 + 1/10000) * L)
        + 1250 * (L * xyRe (-1) (4 * γ * L) + xyT.f 0 * (1 / 10000) * L) :=
      le_trans hpos hsum
    rwa [hid] at h0
  -- ===== the sup-estimates conclude =====
  have hX : 0 ≤ xyMain (Work.LinnikContract.lamOf q ρ₁)
      + xySup1 (Work.LinnikContract.lamOf q ρ₁) (2 * γ * L)
      + xySup2 (Work.LinnikContract.lamOf q ρ₁) (4 * γ * L) + 20 := by
    have h1 : L * (xyMain (Work.LinnikContract.lamOf q ρ₁)
          + xySup1 (Work.LinnikContract.lamOf q ρ₁) (2 * γ * L)
          + xySup2 (Work.LinnikContract.lamOf q ρ₁) (4 * γ * L))
        + L * (xyT.f 0 * 61009 * (1 / 10000))
        = L * (xyMain (Work.LinnikContract.lamOf q ρ₁)
          + xySup1 (Work.LinnikContract.lamOf q ρ₁) (2 * γ * L)
          + xySup2 (Work.LinnikContract.lamOf q ρ₁) (4 * γ * L)
          + xyT.f 0 * 61009 * (1 / 10000)) := by ring
    rw [h1] at hcomb
    have h2 : 0 ≤ xyMain (Work.LinnikContract.lamOf q ρ₁)
        + xySup1 (Work.LinnikContract.lamOf q ρ₁) (2 * γ * L)
        + xySup2 (Work.LinnikContract.lamOf q ρ₁) (4 * γ * L)
        + xyT.f 0 * 61009 * (1 / 10000) := (mul_nonneg_iff_of_pos_left hLpos).mp hcomb
    have h3 : xyT.f 0 * 61009 * (1 / 10000) ≤ 20 := by rw [xyT_f_zero]; norm_num
    linarith
  have hs1 := (SupBoundOrd2 (Work.LinnikContract.lamOf q ρ₁) (2 * γ * L) hlam_lo hlam_hi).1
  have hs2 := (SupBoundOrd2 (Work.LinnikContract.lamOf q ρ₁) (4 * γ * L) hlam_lo hlam_hi).2
  linarith

end Work.ZeroFreeTables.XY
