import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIArea6Hecke.R.LogDerivStatementDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.R.oneSidedToTwoSided
import Submission.Work.FIArea6Hecke.R.heckeLval_logDeriv_norm_le_of_one_lt_re
import Submission.Work.FIArea6Hecke.R.heckeStripArithConst
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor
import Submission.Work.FIArea6Hecke.R.zfrOffAxisSdMine
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.zfrRealAxisSd
import Submission.Work.FIArea6Hecke.R.heckeFECleanNamespaced

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Complex Metric

noncomputable section

/-! **The Borel–Carathéodory assembly.**  The target `heckeStripLogDeriv` follows from the three
analytic inputs

* `hOne : LogDerivReLower ε` — the one-sided real-part bound
  `Re((Lval)'(s)/Lval s) ≥ -C₁·log(4d(|m|+|s.im|+3))` for `re s ≤ 2` (`R/LogDerivStatementDefs`);
* the elementary Dirichlet-series bound `‖(Lval)'(s)/Lval s‖ ≤ C₂(1/(re s - 1) +
  log(4d(|m|+|s.im|+3)))` for `1 < re s ≤ 2`, now a *theorem*
  (`R/heckeLval_logDeriv_norm_le_of_one_lt_re`, proved);
* `hA : ZFRoffAxis`, `hB : ZFRrealAxis ε` — the two zero-free region inputs
  (`R/ZFRStatementDefs`), used to know that `Lval` is zero-free on the closed ball `Metric.ball cb R`
  below (the constant bookkeeping of the two edges), i.e. that `Lval'/Lval` is analytic there.

**The assembly.**  Fix `(d, chi, m, Lam)` and `s` in the target region, put `t := s.im`,
`ℓ := log(|m| + |t| + 3)` (so `ℓ ≥ log 3 > 1`), `X := d^ε ≥ 1`,
`L4 := log(4d(|m|+|t|+3)) = log(4d) + ℓ`, and let `c` be `κ·min(1,δ)/16` where `κ` is the region
constant of the ball lemma and `δ` the comparison constant of `heckeStripArithConst` (so that the
target's region is contained in the one-sided input's region).  With

  `μ := min (1/log(4d + |m| + |t| + 1)) (1/X)`,  `τ := c/(X·ℓ)`,
  `A := (κ/4)·μ + max 0 (s.re - 1)`,  `R := (κ/2)·μ + 2τ`,  `cb := (1+A) + i·t`,

one has `Lval` analytic and zero-free on `Metric.ball cb R`, `‖s - cb‖ ≤ R/2`:

* `‖s - cb‖ = |s.re - 1 - A| ≤ τ + (κ/4)μ = R/2`, since `s.re ≥ 1 - τ` (target region) and
  `s.re - 1 < 1/L` in the case at hand;
* the one-sided input holds on the ball and `Re(-Lval'/Lval) ≤ C·L4` there (ball lemma);
* the centre bound gives `‖F cb‖ ≤ C₂(1/A + L4) ≤ C₂(4/κ + 1)·(L4 + X)`, using
  `1/μ ≤ L4 + X` (i.e. `μ·(L4+X) ≥ 1`, from `logp ≤ L4` and `X ≥ 1`);
* `norm_le_of_re_le_center` (`R/oneSidedToTwoSided`) then concludes
  `‖Lval'/Lval s‖ ≤ 5(C·L4 + C₂(1/A + L4)) ≤ K·(L4 + X)`.

The `+ d^ε` of the target is thus exactly the `1/(cb.re - 1) = 1/A` term in the regime
`d^ε ≫ log(4d+|m|+|t|)`, where the exceptional real zero forces the centre to sit `≍ d^{-ε}` above
`1`; in the other regime `μ` is logarithmic and `1/A ≍ log(4d(|m|+|t|+3))`. -/

/-- **The contract of the ball lemma** `R/heckeStripBallRegions`: the region constant `κ` and the
bound constant `C` together with the two conclusions on every admissible ball. -/
private def BallFacts (ε : ℝ) : Prop :=
  ∃ κ C : ℝ, 0 < κ ∧ κ ≤ 1 / 8 ∧ 0 < C ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ) (t γ R : ℝ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      1 < γ → γ + R ≤ 2 → 0 < R → R ≤ 1 →
      1 - (κ / 2) * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t| + 1))
          (1 / (d : ℝ) ^ ε) ≤ γ - R →
      (∀ w : ℂ, ‖w - ((γ : ℂ) + (t : ℂ) * Complex.I)‖ < R →
          Work.FIArea6Hecke.Lval d m Lam w ≠ 0) ∧
      (∀ w : ℂ, ‖w - ((γ : ℂ) + (t : ℂ) * Complex.I)‖ < R →
          -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)))
            ≤ (deriv (Work.FIArea6Hecke.Lval d m Lam) w
                / Work.FIArea6Hecke.Lval d m Lam w).re)

/-- **The contract of the arithmetic comparison** `R/heckeStripArithConst`. -/
private def ArithFact (ε : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ (d : ℕ) (P : ℝ), 1 ≤ d → 0 ≤ P →
      δ * Real.log (4 * (d : ℝ) + P + 1) ≤ (d : ℝ) ^ ε * Real.log (P + 3)

/-- Analyticity of `-Lval'/Lval` on a ball inside `re > 0` on which `Lval` does not vanish. -/
private lemma analyticOnNhd_neg_deriv_div_Lval {d : ℕ} {m : ℤ} {Lam : ℂ → ℂ} {cb : ℂ} {R : ℝ}
    (hd : 1 ≤ d) (hAn : AnalyticOn ℂ Lam Set.univ)
    (hre : ∀ w ∈ Metric.ball cb R, (1 : ℝ) / 2 ≤ w.re)
    (hne : ∀ w ∈ Metric.ball cb R, Work.FIArea6Hecke.Lval d m Lam w ≠ 0) :
    AnalyticOnNhd ℂ
      (fun w => -(deriv (Work.FIArea6Hecke.Lval d m Lam) w
        / Work.FIArea6Hecke.Lval d m Lam w)) (Metric.ball cb R) := by
  have hLval_diff : DifferentiableOn ℂ (Work.FIArea6Hecke.Lval d m Lam) (Metric.ball cb R) := by
    have hLam : DifferentiableOn ℂ Lam (Metric.ball cb R) :=
      (analyticOn_univ.mp hAn).differentiableOn.mono (Set.subset_univ _)
    have harch : DifferentiableOn ℂ (Work.FITop4.Bridge.heckeArch d m) (Metric.ball cb R) := by
      intro w hw
      exact (Work.FIArea6Hecke.R.heckeArch_differentiableAt_of_pos hd m
        (lt_of_lt_of_le (by norm_num) (hre w hw))).differentiableWithinAt
    exact hLam.div harch (fun w hw =>
      Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd m
        (lt_of_lt_of_le (by norm_num) (hre w hw)))
  refine DifferentiableOn.analyticOnNhd ?_ Metric.isOpen_ball
  exact ((hLval_diff.deriv Metric.isOpen_ball).div hLval_diff hne).neg

private theorem strip_core_of_ball_facts (ε : ℝ) (hε : 0 < ε)
    (hball : BallFacts ε) (harith : ArithFact ε) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ∀ s : ℂ,
          1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re → s.re ≤ 2 →
          ‖deriv (Work.FIArea6Hecke.Lval d m Lam) s / Work.FIArea6Hecke.Lval d m Lam s‖
            ≤ K * (Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) + (d : ℝ) ^ ε) := by
  obtain ⟨κ, C, hκpos, hκ8, hCpos, hball'⟩ := hball
  obtain ⟨δ, hδpos, hδ1, harith'⟩ := harith
  obtain ⟨C₂, hC₂pos, hdir⟩ := heckeLval_logDeriv_norm_le_of_one_lt_re
  refine ⟨κ * min 1 δ / 16, 5 * (C + C₂ * (4 / κ + 1)) + 2 * C₂, ?_, ?_, ?_⟩
  · positivity
  · positivity
  intro d chi m Lam hd hchi hAn hagr s hsreg hsle2
  set X : ℝ := (d : ℝ) ^ ε with hX
  set l : ℝ := Real.log (|(m : ℝ)| + |s.im| + 3) with hl
  set L4 : ℝ := Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) with hL4
  set logp : ℝ := Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1) with hlogp
  set mu : ℝ := min (1 / logp) (1 / X) with hmu
  set tau : ℝ := (κ * min 1 δ / 16) / (X * l) with htau
  set L : ℝ := L4 + X with hL
  have hsreg' : 1 - tau ≤ s.re := hsreg
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hX1 : 1 ≤ X := by
    rw [hX]; exact Real.one_le_rpow hd1 hε.le
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hP0 : (0 : ℝ) ≤ |(m : ℝ)| + |s.im| := by positivity
  have hlogp1 : 1 < logp := by
    rw [hlogp]
    have h5 : (5 : ℝ) ≤ 4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1 := by linarith
    have h1 : (1 : ℝ) < Real.log 5 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 5)]
      exact lt_trans Real.exp_one_lt_three (by norm_num)
    exact lt_of_lt_of_le h1 (Real.log_le_log (by norm_num) h5)
  have hlogppos : 0 < logp := lt_trans zero_lt_one hlogp1
  have hl1 : 1 ≤ l := by
    rw [hl]
    have h3 : (3 : ℝ) ≤ |(m : ℝ)| + |s.im| + 3 := by linarith
    have h1 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact le_trans h1.le (Real.log_le_log (by norm_num) h3)
  have hlpos : 0 < l := lt_of_lt_of_le zero_lt_one hl1
  have hXlpos : 0 < X * l := mul_pos hXpos hlpos
  have hlogpL4 : logp ≤ L4 := by
    rw [hlogp, hL4]
    refine Real.log_le_log (by positivity) ?_
    nlinarith [hP0, hd1]
  have hL4pos : 0 < L4 := lt_of_lt_of_le zero_lt_one (le_trans hlogp1.le hlogpL4)
  have hLge : 2 ≤ L := by
    rw [hL]
    have h12 : (2 : ℝ) < Real.log 12 := by
      have hp : Real.log ((3 : ℝ) ^ 2) = 2 * Real.log 3 := by
        rw [Real.log_pow]; norm_num
      have h9 : Real.log (9 : ℝ) < Real.log 12 := Real.log_lt_log (by norm_num) (by norm_num)
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, hp] at h9
      linarith [Real.log_three_gt_d9]
    have h12le : Real.log 12 ≤ L4 := by
      rw [hL4]
      refine Real.log_le_log (by norm_num) ?_
      nlinarith [hP0, hd1]
    linarith
  have h1L : 1 / L ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hLge
  have hmu_pos : 0 < mu := by
    rw [hmu]; exact lt_min (by positivity) (by positivity)
  have hmu_le_one : mu ≤ 1 := by
    have h1 : mu ≤ 1 / X := by rw [hmu]; exact min_le_right _ _
    have h2 : (1 : ℝ) / X ≤ 1 := by
      rw [one_div]; exact inv_le_one_of_one_le₀ hX1
    linarith
  have hmin1δ_pos : 0 < min 1 δ := lt_min zero_lt_one hδpos
  have hmin1δ_le_one : min 1 δ ≤ 1 := min_le_left _ _
  have hc_ub : κ * min 1 δ / 16 ≤ 1 / 128 := by
    have h1 : κ * min 1 δ ≤ 1 / 8 := by nlinarith [hκ8, hmin1δ_le_one, hmin1δ_pos, hκpos]
    linarith
  have htau_le : tau ≤ 1 / 128 := by
    rw [htau, div_le_iff₀ hXlpos]
    have hXl1 : (1 : ℝ) ≤ X * l := by nlinarith [hX1, hl1]
    nlinarith [hc_ub, hXl1]
  have hmuL : 1 ≤ mu * (L4 + X) := by
    rw [hmu]
    rcases le_total (1 / logp) (1 / X) with h | h
    · rw [min_eq_left h, one_div]
      rw [le_inv_mul_iff₀ hlogppos]
      linarith [hlogpL4]
    · rw [min_eq_right h, one_div]
      rw [le_inv_mul_iff₀ hXpos]
      linarith
  have hkey : min 1 δ / 2 ≤ X * l * mu := by
    have hXlmu : X * l * mu = min (X * l / logp) l := by
      rw [hmu, mul_min_of_nonneg]
      · congr 1
        · field_simp
        · field_simp
      · positivity
    rw [hXlmu]
    have hm1 : min 1 δ ≤ X * l / logp := by
      refine le_trans (min_le_right 1 δ) ?_
      rw [le_div_iff₀ hlogppos]
      have h := harith' d (|(m : ℝ)| + |s.im|) hd hP0
      have he : Real.log (4 * (d : ℝ) + (|(m : ℝ)| + |s.im|) + 1) = logp := by
        rw [hlogp]; congr 1; ring
      rw [he] at h
      simpa [hX, hl] using h
    have hm2 : min 1 δ ≤ l := le_trans (min_le_left 1 δ) hl1
    have hm0 : 0 ≤ min 1 δ := le_of_lt hmin1δ_pos
    have := le_min hm1 hm2
    linarith
  have htau_nn : 0 ≤ tau := by rw [htau]; positivity
  have h2tau : 2 * tau ≤ (κ / 4) * mu := by
    rw [htau]
    rw [show 2 * (κ * min 1 δ / 16 / (X * l)) = (2 * (κ * min 1 δ / 16)) / (X * l) by ring]
    rw [div_le_iff₀ hXlpos]
    nlinarith [hkey, hκpos]
  rcases le_total (1 / L) (s.re - 1) with hcase | hcase
  · -- Case A: `s` is to the right of `1 + 1/L`: the crude Dirichlet bound suffices.
    have hs1 : 1 < s.re := by
      have h1Lpos : (0 : ℝ) < 1 / L := by positivity
      linarith
    have hdir' := hdir d chi m Lam hd hchi hAn hagr s hs1 hsle2
    have hinv : 1 / (s.re - 1) ≤ L := by
      have hsr : (0 : ℝ) < s.re - 1 := by linarith
      have hLpos : (0 : ℝ) < L := by linarith [hLge]
      rw [div_le_iff₀ hsr]
      rw [div_le_iff₀ hLpos] at hcase
      linarith [hcase]
    have hL4L : L4 ≤ L := by rw [hL]; linarith
    have hfin : C₂ * (1 / (s.re - 1) + L4) ≤
        (5 * (C + C₂ * (4 / κ + 1)) + 2 * C₂) * (L4 + X) := by
      have h1 : 1 / (s.re - 1) + L4 ≤ 2 * L := by linarith
      have h2 : C₂ * (1 / (s.re - 1) + L4) ≤ C₂ * (2 * L) :=
        mul_le_mul_of_nonneg_left h1 hC₂pos.le
      have h3 : C₂ * (2 * L) ≤ (5 * (C + C₂ * (4 / κ + 1)) + 2 * C₂) * (L4 + X) := by
        have h5 : 0 ≤ 5 * (C + C₂ * (4 / κ + 1)) := by positivity
        rw [hL] at h2 ⊢
        nlinarith [h2, h5, hC₂pos, hL4pos, hXpos]
      linarith
    linarith [hdir', hfin]
  · -- Case B: the ball argument.
    have hcase' : s.re - 1 ≤ 1 / L := hcase
    set A : ℝ := (κ / 4) * mu + max 0 (s.re - 1) with hA_
    set R : ℝ := (κ / 2) * mu + 2 * tau with hR
    set γ : ℝ := 1 + A with hγ
    have hApos : 0 < A := by
      rw [hA_]
      have := mul_pos (by positivity : (0 : ℝ) < κ / 4) hmu_pos
      linarith [le_max_left (0 : ℝ) (s.re - 1)]
    have hγ1 : 1 < γ := by rw [hγ]; linarith
    have hRpos : 0 < R := by rw [hR]; positivity
    have hleft : 1 - (κ / 2) * mu ≤ γ - R := by
      rw [hγ, hA_, hR]
      linarith [h2tau, le_max_left (0 : ℝ) (s.re - 1)]
    have hγR : γ + R ≤ 2 := by
      rw [hγ, hR, hA_]
      have hmax : max 0 (s.re - 1) ≤ 1 / L := by
        rw [max_le_iff]; exact ⟨by positivity, hcase'⟩
      have h1 : (κ / 4) * mu ≤ 1 / 32 := by nlinarith [hκ8, hmu_le_one, hmu_pos]
      have h2 : (κ / 2) * mu ≤ 1 / 16 := by nlinarith [hκ8, hmu_le_one, hmu_pos]
      have h4 : 2 * tau ≤ 1 / 64 := by linarith [htau_le]
      linarith [h1L]
    have hRle1 : R ≤ 1 := by linarith
    obtain ⟨hballne, hballbd⟩ :=
      hball' d chi m Lam s.im γ R hd hchi hAn hagr hγ1 hγR hRpos hRle1 hleft
    set cb : ℂ := (γ : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I with hcb
    have hcb_re : cb.re = γ := by
      rw [hcb]; simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have hcb_im : cb.im = s.im := by
      rw [hcb]; simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have hmem : ∀ w : ℂ, w ∈ Metric.ball cb R → ‖w - cb‖ < R := by
      intro w hw; rwa [Metric.mem_ball, dist_eq_norm] at hw
    have hne : ∀ w ∈ Metric.ball cb R, Work.FIArea6Hecke.Lval d m Lam w ≠ 0 :=
      fun w hw => hballne w (hmem w hw)
    have hre_half : ∀ w ∈ Metric.ball cb R, (1 : ℝ) / 2 ≤ w.re := by
      intro w hw
      have h1 : ‖w - cb‖ < R := hmem w hw
      have h2 : |w.re - cb.re| ≤ ‖w - cb‖ := by
        simpa using Complex.abs_re_le_norm (w - cb)
      have h3 : |w.re - γ| < R := by
        rw [hcb_re] at h2; linarith
      have h4 : γ - R ≤ w.re := by
        have := (abs_lt.mp h3).1; linarith
      have h6 : (κ / 2) * mu ≤ 1 / 16 := by nlinarith [hκ8, hmu_le_one, hmu_pos]
      linarith
    have hzan : AnalyticOnNhd ℂ
        (fun w => -(deriv (Work.FIArea6Hecke.Lval d m Lam) w
          / Work.FIArea6Hecke.Lval d m Lam w)) (Metric.ball cb R) :=
      analyticOnNhd_neg_deriv_div_Lval hd hAn hre_half hne
    have hBnd : ∀ w ∈ Metric.ball cb R,
        (-(deriv (Work.FIArea6Hecke.Lval d m Lam) w
          / Work.FIArea6Hecke.Lval d m Lam w)).re ≤ C * L4 := by
      intro w hw
      have h := hballbd w (hmem w hw)
      rw [Complex.neg_re, hL4]
      linarith
    have hcent : ‖-(deriv (Work.FIArea6Hecke.Lval d m Lam) cb
        / Work.FIArea6Hecke.Lval d m Lam cb)‖ ≤ C₂ * (1 / A + L4) := by
      have hcb1 : 1 < cb.re := by rw [hcb_re]; exact hγ1
      have hcb2 : cb.re ≤ 2 := by rw [hcb_re]; linarith
      have h := hdir d chi m Lam hd hchi hAn hagr cb hcb1 hcb2
      have hlog_eq : Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |cb.im| + 3)) = L4 := by
        rw [hcb_im, hL4]
      rw [hcb_re, hlog_eq] at h
      have hγ1' : γ - 1 = A := by rw [hγ]; ring
      rw [hγ1'] at h
      rw [norm_neg]
      exact h
    have hA_ge : (κ / 4) * mu ≤ A := by
      rw [hA_]; exact le_add_of_nonneg_right (le_max_left (0 : ℝ) (s.re - 1))
    have h1A : 1 / A ≤ (4 / κ) * (L4 + X) := by
      have hmu_inv : 1 / mu ≤ L4 + X := by
        rw [div_le_iff₀ hmu_pos]; linarith [hmuL]
      have h1 : 1 / A ≤ 1 / ((κ / 4) * mu) := by
        rw [one_div, one_div]
        exact inv_anti₀ (mul_pos (by positivity) hmu_pos) hA_ge
      have h2 : 1 / ((κ / 4) * mu) = (4 / κ) * (1 / mu) := by
        field_simp
      have h3 : (4 / κ) * (1 / mu) ≤ (4 / κ) * (L4 + X) :=
        mul_le_mul_of_nonneg_left hmu_inv (by positivity)
      linarith [h1, h2.le, h2.ge, h3]
    have hs_cb : ‖s - cb‖ ≤ R / 2 := by
      have hsub : s - cb = ((s.re - γ : ℝ) : ℂ) := by
        rw [hcb]
        apply Complex.ext
        · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
        · simp [Complex.sub_im, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [hsub, Complex.norm_real, Real.norm_eq_abs]
      have hR2 : R / 2 = (κ / 4) * mu + tau := by rw [hR]; ring
      rw [hR2]
      rcases le_total (1 : ℝ) s.re with hσ | hσ
      · have hmax : max 0 (s.re - 1) = s.re - 1 := max_eq_right (by linarith)
        have heq : s.re - γ = -((κ / 4) * mu) := by rw [hγ, hA_, hmax]; ring
        rw [heq, abs_neg, abs_of_pos (by positivity)]
        linarith [htau_nn]
      · have hmax : max 0 (s.re - 1) = 0 := max_eq_left (by linarith)
        have heq : s.re - γ = -((κ / 4) * mu + (1 - s.re)) := by rw [hγ, hA_, hmax]; ring
        rw [heq, abs_neg, abs_of_pos (by linarith [hmu_pos])]
        have hle : 1 - s.re ≤ tau := by linarith
        linarith [hle, htau_nn]
    have hmain := norm_le_of_re_le_center
      (F := fun w => -(deriv (Work.FIArea6Hecke.Lval d m Lam) w
        / Work.FIArea6Hecke.Lval d m Lam w))
      (c := cb) (R := R) (Bnd := C * L4) (Bndc := C₂ * (1 / A + L4))
      hRpos (by positivity) (by positivity) hzan hBnd hcent s hs_cb
    rw [norm_neg] at hmain
    have hstep : C₂ * (1 / A + L4) ≤ C₂ * ((4 / κ) * (L4 + X) + (L4 + X)) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₂pos.le
      have hL4L : L4 ≤ L4 + X := by linarith [hXpos]
      linarith [h1A, hL4L]
    have hfinal : 5 * (C * L4 + C₂ * (1 / A + L4))
        ≤ (5 * (C + C₂ * (4 / κ + 1)) + 2 * C₂) * (L4 + X) := by
      have hL4L : L4 ≤ L4 + X := by linarith [hXpos]
      nlinarith [hstep, hL4L, hCpos, hC₂pos, hL4pos, hXpos]
    linarith [hmain, hfinal]

/-- **The Borel–Carathéodory assembly.**  Proved from `R/strip_core_of_ball_facts` together with
the two delegated inputs `R/heckeStripBallRegions` (the ball regions) and `R/heckeStripArithConst`
(the comparison of the two logarithmic scales). -/
theorem heckeStripLogDeriv_of_inputs (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hOne : Work.FIArea6Hecke.R.LogDerivReLower ε)
    (hA : Work.FIArea6Hecke.R.ZFRoffAxisSd)
    (hB : Work.FIArea6Hecke.R.ZFRrealAxisSd ε) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ∀ s : ℂ,
          1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re → s.re ≤ 2 →
          ‖deriv (Work.FIArea6Hecke.Lval d m Lam) s / Work.FIArea6Hecke.Lval d m Lam s‖
            ≤ K * (Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) + (d : ℝ) ^ ε) := by
  exact strip_core_of_ball_facts ε hε (heckeStripBallRegionsSdMine ε hε hOne hA hB)
    (heckeStripArithConst ε hε hε4)

/-- **The logarithmic-derivative bound inside the zero-free region** (*FI* (16.23)'s companion, the
input of the `L'/L`-integration route to the inverse bound): there are `c, K > 0` such that for
every entire completion `Lam` of the Hecke `L`-function of `ℚ(i)` (`Lam s = heckeArch d m s ·
heckeLSeries χ m s` for `re s > 1 + |m|/2`), every strict `χ` mod `4d` and every `m : ℤ`,

  `‖(Lval d m Lam)'(s)/Lval d m Lam s‖ ≤ K(log(4d(|m|+|s.im|+3)) + d^ε)`

for `1 - c/(d^ε log(|m|+|s.im|+3)) ≤ re s ≤ 2`.  This is the second conjunct of `StripCore ε`
(`StripCoreDefs.lean`).

The `+ d^ε` correction is the exceptional-zero term (cf. *FI* (16.23)); the depth
`c/(d^ε log(…))` is the same deep input as in the companion `heckeStripZFR` (Landau–Siegel for the
real zero).


**The functional-equation input.**  The chain is closed against the conductor-normalised functional
equation `Work.FIArea6Hecke.RF.conductorFECleanRF` (`R/heckeFECleanNamespaced.lean`), an
axiom-clean namespaced copy of `R/conductorFEClean.lean`.  The copy is needed because
`R/conductorFEClean.lean` declares the name `Work.FIArea6Hecke.R.hasConductorFE_conj`, which the
still-`sorry`-carrying delegated stub `R/hasConductorFE_conj.lean` also declares; the stub is
reachable from this file's graph (through `R/zerosInStrip.lean` →
`R/heckeFEStrictConductorUni.lean`), so importing `conductorFEClean` itself is rejected by Lean
("environment already contains ...").  The namespaced copy avoids the collision.

**Proof status.**  The assembly `heckeStripLogDeriv_of_inputs` (proved, in this file) derives the
statement from

* `hOne : LogDerivReLower ε` — the one-sided bound `Re((Lval)'(s)/Lval s) ≥ -C₁·log(4d(|m|+|s.im|+3))`
  (*FI* (16.20)/(16.23));
* an off-axis zero-free region and a real-axis (Siegel) bound, used to know that the ball of the
  Borel–Carathéodory argument in `strip_core_of_ball_facts` is free of zeros.

**The zero-free-region inputs must carry the *correct* exceptional set.**  The design of
`R/ZFRStatementDefs.lean` phrased the off-axis input with the exceptional set
`PsiReal χ m` (`ψ` real on *all* of `ℤ[i]`), which is too narrow: twisting a real character by a
character trivial on the primary coset keeps the Hecke eigenvalues (hence the `L`-series, hence the
zero set) but destroys `PsiReal`, so that version would forbid the Landau–Siegel zero of a genuinely
real Hecke `L`-function.  The correction (found by the prover of `R/zfrOffAxisClean`, see
`R/NOTES_zfrInterfaceFix.md`) replaces the exceptional set by the self-duality condition
`SelfDual d chi m` (`ψ = ±1` on the primary units, i.e. real Hecke eigenvalues), giving the
statements `ZFRoffAxisSd` and `ZFRrealAxisSd ε` of `R/heckeStripLogDerivConductor`.  This file uses
those corrected inputs throughout:

* `R/heckeStripLogDerivConductor.lean` — the definitions `SelfDual`, `ZFRoffAxisSd`,
  `ZFRrealAxisSd`, the corrected copies `logDerivReLowerSd_of`, `logDerivReLowerSd_of_baseBounds`
  of the `L'/L` assembly of `R/logDerivCore` (case split on `SelfDual`), the ball-region lemma
  `heckeStripBallRegionsSdMine`, and the capstone
  `logDerivReLower_of_conductorFESd` producing `LogDerivReLower ε` from
  `ZFRoffAxisSd`, `ZFRrealAxisSd ε` and the conductor-normalised functional equation
  (`zerosInStrip_of_conductorFE`, `baseLowerNegTwoUniform_of_conductorFE`, `baseLowerTwoUniform`,
  `lamPartialFraction` via `lamGrowth`, `lam_logDeriv_re_at_two_le_uniform`);
* `R/zfrOffAxisSdMine.lean`, `R/zfrRealAxisSd.lean` — the two corrected zero-free-region inputs;
* `R/exists_real_pair_of_selfDual.lean` — the transfer of a self-dual pair to a real one (same
  Hecke eigenvalues), used by `zfrRealAxisSd` and by the self-dual case of `zfrOffAxisSd`;
* `R/conductorFEClean.lean` — the conductor-normalised functional equation for arbitrary strict `χ`
  (the clean replacement for the two stubs `R/levelHeckeFE` + `R/heckePartnerThetaLaw` behind
  `R/heckeFEStrictConductorUni`).
-/
theorem heckeStripLogDeriv (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ∀ s : ℂ,
          1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) ≤ s.re → s.re ≤ 2 →
          ‖deriv (Work.FIArea6Hecke.Lval d m Lam) s / Work.FIArea6Hecke.Lval d m Lam s‖
            ≤ K * (Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) + (d : ℝ) ^ ε) :=
  heckeStripLogDeriv_of_inputs ε hε hε4
    (logDerivReLower_of_conductorFESd ε hε hε4 Work.FIArea6Hecke.RF.conductorFECleanRF zfrOffAxisSdMine
      (zfrRealAxisSd ε hε hε4))
    zfrOffAxisSdMine (zfrRealAxisSd ε hε hε4)

end

end Work.FIArea6Hecke.R
