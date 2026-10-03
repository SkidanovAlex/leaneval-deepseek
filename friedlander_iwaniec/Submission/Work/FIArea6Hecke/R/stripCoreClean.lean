import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIArea6Hecke.R.LogDerivStatementDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.R.oneSidedToTwoSided
import Submission.Work.FIArea6Hecke.R.heckeLval_logDeriv_norm_le_of_one_lt_re
import Submission.Work.FIArea6Hecke.R.heckeStripArithConst
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne

/-!
# `Submission.Work.FIArea6Hecke.R.stripCoreClean`

The Borel--Caratheodory assembly giving the **norm bound** for `(Lval d m Lam)'/Lval d m Lam` in
the zero-free region, from the one-sided input `Work.FIArea6Hecke.R.LogDerivReLower`,
the off-axis region `Work.FIArea6Hecke.R.ZFRoffAxisSd` and the real-axis input
`Work.FIArea6Hecke.R.ZFRrealAxisSd`.

It is a copy (all declarations renamed `Sc*` / `heckeStripLogDerivOfInputs`) of the assembly
`Work.FIArea6Hecke.R.heckeStripLogDeriv_of_inputs` in `R/heckeStripLogDeriv.lean`, made so that the
target `Work.FIArea6Hecke.R.heckeLSeries_logDeriv_bound_re_gt_one` does not depend on that module,
whose import list is periodically broken by unrelated edits (e.g. the `hasConductorFE_conj` /
`conductorFEClean` name collision).  Every mathematical ingredient
(`Work.FIArea6Hecke.R.heckeStripBallRegionsSdMine`, `Work.FIArea6Hecke.R.heckeStripArithConst`,
`Work.FIArea6Hecke.R.norm_le_of_re_le_center`,
`Work.FIArea6Hecke.R.heckeLval_log_deriv_norm_le_of_one_lt_re`) is imported from its own module.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Complex Metric

noncomputable section

/-- **The contract of the ball lemma** `R/heckeStripBallRegions`: the region constant `κ` and the
bound constant `C` together with the two conclusions on every admissible ball. -/
private def ScBallFacts (ε : ℝ) : Prop :=
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
private def ScArithFact (ε : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ (d : ℕ) (P : ℝ), 1 ≤ d → 0 ≤ P →
      δ * Real.log (4 * (d : ℝ) + P + 1) ≤ (d : ℝ) ^ ε * Real.log (P + 3)

/-- Analyticity of `-Lval'/Lval` on a ball inside `re > 0` on which `Lval` does not vanish. -/
private lemma sc_analyticOnNhd_neg_deriv_div_Lval {d : ℕ} {m : ℤ} {Lam : ℂ → ℂ} {cb : ℂ} {R : ℝ}
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

private theorem sc_strip_core_of_ball_facts (ε : ℝ) (hε : 0 < ε)
    (hball : ScBallFacts ε) (harith : ScArithFact ε) :
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
      sc_analyticOnNhd_neg_deriv_div_Lval hd hAn hre_half hne
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

/-- **The Borel–Carathéodory assembly.**  Proved from `R/sc_strip_core_of_ball_facts` together with
the two delegated inputs `R/heckeStripBallRegions` (the ball regions) and `R/heckeStripArithConst`
(the comparison of the two logarithmic scales). -/
theorem heckeStripLogDerivOfInputs (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
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
  exact sc_strip_core_of_ball_facts ε hε (heckeStripBallRegionsSdMine ε hε hOne hA hB)
    (heckeStripArithConst ε hε hε4)
end

end Work.FIArea6Hecke.R
