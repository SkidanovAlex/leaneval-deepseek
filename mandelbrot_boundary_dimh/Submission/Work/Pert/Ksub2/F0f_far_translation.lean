import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.F0f_eq_model
import Submission.Work.Pert.Ksub2.differentiableAt_F0f_of_local
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.Pert.Ksub2.norm_sub_le_of_deriv_close_far
import Submission.Work.Pert.Ksub2.deriv_div_tau0_model

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Elementary facts about `τ₀ w = -1/w` -/

private lemma tau0_tau0 (v : ℂ) : MandelDim.tau0 (MandelDim.tau0 v) = v := by
  simp [MandelDim.tau0]

private lemma norm_tau0 (v : ℂ) : ‖MandelDim.tau0 v‖ = 1 / ‖v‖ := by
  simp [MandelDim.tau0]

private lemma tau0_mul_self {w : ℂ} (hw : w ≠ 0) : w * MandelDim.tau0 w = -1 := by
  simp only [MandelDim.tau0]
  field_simp

private lemma continuousAt_tau0 {w : ℂ} (hw : w ≠ 0) : ContinuousAt MandelDim.tau0 w := by
  show ContinuousAt (fun v : ℂ => -1 / v) w
  exact continuousAt_const.div continuousAt_id hw

/-- `τ₀` is multiplicative in the sense `τ₀ (a b) = τ₀ a / b`. -/
private lemma tau0_mul (a b : ℂ) : MandelDim.tau0 (a * b) = MandelDim.tau0 a / b := by
  rw [MandelDim.tau0, MandelDim.tau0, div_div]

/-! ## The `hF`-model of `F0f` -/

/-- The value of the limit dynamics in terms of the model germ `f₀ u = u + u² hF u` at
`u = τ₀ w`: `F0f f₀ w = w / (1 + τ₀ w · hF (τ₀ w))`. -/
private lemma F0f_eq_div {f₀ hF : ℂ → ℂ} {w : ℂ}
    (hfe : f₀ (MandelDim.tau0 w)
      = MandelDim.tau0 w + MandelDim.tau0 w ^ 2 * hF (MandelDim.tau0 w)) :
    Work.Pert.F0f f₀ w = w / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) := by
  have h1 : MandelDim.tau0 w + MandelDim.tau0 w ^ 2 * hF (MandelDim.tau0 w)
      = MandelDim.tau0 w * (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) := by ring
  have h2 : MandelDim.tau0 (MandelDim.tau0 w * (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)))
      = w / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) := by
    rw [tau0_mul, tau0_tau0]
  show MandelDim.tau0 (f₀ (MandelDim.tau0 w)) = _
  rw [hfe, h1, h2]

/-- Subtraction algebra: the translation defect in the model form. -/
private lemma div_sub_one_algebra {w t h : ℂ} (hwt : w * t = -1) (hden : 1 + t * h ≠ 0) :
    w / (1 + t * h) - (w + 1) = (h - 1 - t * h) / (1 + t * h) := by
  field_simp
  linear_combination (-h) * hwt

/-- The model data of a parabolic germ: `f₀ u = u + u² hF u` near `0`, with `hF`, `hF'` bounded. -/
private lemma exists_model_data {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ hF : ℂ → ℂ, ∃ b : ℂ, ∃ r' A'' A''' : ℝ, 0 < r' ∧ 0 ≤ A'' ∧ 0 ≤ A''' ∧
      (∀ u ∈ Metric.ball (0 : ℂ) r', f₀ u = u + u ^ 2 * hF u) ∧
      DifferentiableOn ℂ hF (Metric.ball (0 : ℂ) r') ∧
      (∀ u ∈ Metric.ball (0 : ℂ) r', ‖hF u - 1 - b * u‖ ≤ A'' * ‖u‖ ^ 2) ∧
      hF 0 = 1 ∧
      (∀ u ∈ Metric.ball (0 : ℂ) r', ‖hF u‖ ≤ 2) ∧
      (∀ u ∈ Metric.ball (0 : ℂ) r', ‖deriv hF u‖ ≤ A''') := by
  obtain ⟨hDopen, h0D, hdiff, hf0, hd1, hd2⟩ := hd
  have hFan : AnalyticAt ℂ f₀ 0 := hdiff.analyticAt (hDopen.mem_nhds h0D)
  have hF1 : iteratedDeriv 1 f₀ 0 = 1 := by rw [iteratedDeriv_one]; exact hd1
  have hF2 : iteratedDeriv 2 f₀ 0 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]; exact hd2
  obtain ⟨hF, r', A'', A''', hr', hA''nn, hA'''nn, hFeq, hFdiff, hFclose, hFbnd, hFderiv⟩ :=
    Work.FatouCoord.Petal.exists_parabolic_germ_bounds (b := iteratedDeriv 3 f₀ 0 / 6)
      hFan hf0 hF1 hF2 (by ring_nf)
  have hF0 : hF 0 = 1 := by
    have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r' := by
      rw [Metric.mem_ball, dist_self]; exact hr'
    have h := hFclose 0 h0
    have h2 : ‖hF 0 - 1‖ ≤ 0 := by simpa using h
    have h3 : ‖hF 0 - 1‖ = 0 := le_antisymm h2 (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  exact ⟨hF, iteratedDeriv 3 f₀ 0 / 6, r', A'', A''', hr', hA''nn, hA'''nn, hFeq, hFdiff,
    hFclose, hF0, hFbnd, hFderiv⟩

/-! ## The far-field pointwise estimate -/

private lemma far_pointwise {f₀ hF : ℂ → ℂ} {b : ℂ} {r' A'' A''' δ : ℝ}
    (hr' : 0 < r') (hA''nn : 0 ≤ A'') (hA'''nn : 0 ≤ A''')
    (hFeq : ∀ u ∈ Metric.ball (0 : ℂ) r', f₀ u = u + u ^ 2 * hF u)
    (hFdiff : DifferentiableOn ℂ hF (Metric.ball (0 : ℂ) r'))
    (hFclose : ∀ u ∈ Metric.ball (0 : ℂ) r', ‖hF u - 1 - b * u‖ ≤ A'' * ‖u‖ ^ 2)
    (hFbnd : ∀ u ∈ Metric.ball (0 : ℂ) r', ‖hF u‖ ≤ 2)
    (hFderiv : ∀ u ∈ Metric.ball (0 : ℂ) r', ‖deriv hF u‖ ≤ A''')
    (hδpos : 0 < δ) (hδr : δ ≤ r' / 2) (hδ4 : δ ≤ 1 / 4)
    (hδK : (‖b‖ + A'' + 2) * δ ≤ 1 / 16) :
    ∀ w : ℂ, 1 / δ ≤ ‖w‖ → DifferentiableAt ℂ (Work.Pert.F0f f₀) w ∧
      ‖Work.Pert.F0f f₀ w - (w + 1)‖ ≤ 1 / 8 ∧
      ‖deriv (Work.Pert.F0f f₀) w - 1‖ ≤ 4 * (A''' + 4) / ‖w‖ ^ 2 := by
  intro w hw
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (one_div_pos.mpr hδpos) hw
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hwpos)
  have htnorm : ‖MandelDim.tau0 w‖ ≤ δ := by
    rw [norm_tau0, div_le_iff₀ hwpos]
    have h1 : δ * (1 / δ) ≤ δ * ‖w‖ := mul_le_mul_of_nonneg_left hw hδpos.le
    rwa [mul_one_div, div_self (ne_of_gt hδpos)] at h1
  have htball : MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) r' := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have ht4 : ‖MandelDim.tau0 w‖ ≤ 1 / 4 := le_trans htnorm hδ4
  have hbnd2 : ‖hF (MandelDim.tau0 w)‖ ≤ 2 := hFbnd _ htball
  have htbnd : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ ≤ 1 / 2 := by
    rw [norm_mul]; nlinarith [norm_nonneg (MandelDim.tau0 w), hbnd2]
  have hden_ne : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0 := by
    intro h0
    have h1 : MandelDim.tau0 w * hF (MandelDim.tau0 w) = -1 := by linear_combination h0
    rw [h1, norm_neg, norm_one] at htbnd
    norm_num at htbnd
  have hden_lb : (1 : ℝ) / 2 ≤ ‖1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (-(MandelDim.tau0 w * hF (MandelDim.tau0 w)))
    rw [norm_one, norm_neg, sub_neg_eq_add] at h1
    linarith
  refine ⟨differentiableAt_F0f_of_local hFeq hFdiff hwne htball hden_ne, ?_, ?_⟩
  · -- ## value estimate
    have hfe : f₀ (MandelDim.tau0 w)
        = MandelDim.tau0 w + MandelDim.tau0 w ^ 2 * hF (MandelDim.tau0 w) := hFeq _ htball
    rw [F0f_eq_div hfe, div_sub_one_algebra (tau0_mul_self hwne) hden_ne]
    have hnum : ‖hF (MandelDim.tau0 w) - 1 - MandelDim.tau0 w * hF (MandelDim.tau0 w)‖
        ≤ ‖MandelDim.tau0 w‖ * (‖b‖ + A'' + 2) := by
      have hsplit : hF (MandelDim.tau0 w) - 1 - MandelDim.tau0 w * hF (MandelDim.tau0 w)
          = (hF (MandelDim.tau0 w) - 1) - MandelDim.tau0 w * hF (MandelDim.tau0 w) := by ring
      rw [hsplit]
      have h1 : ‖hF (MandelDim.tau0 w) - 1‖
          ≤ A'' * ‖MandelDim.tau0 w‖ ^ 2 + ‖b‖ * ‖MandelDim.tau0 w‖ := by
        have hsp : hF (MandelDim.tau0 w) - 1
            = (hF (MandelDim.tau0 w) - 1 - b * MandelDim.tau0 w)
              + b * MandelDim.tau0 w := by ring
        calc ‖hF (MandelDim.tau0 w) - 1‖
            = ‖(hF (MandelDim.tau0 w) - 1 - b * MandelDim.tau0 w)
                + b * MandelDim.tau0 w‖ := congrArg norm hsp
          _ ≤ ‖hF (MandelDim.tau0 w) - 1 - b * MandelDim.tau0 w‖
                + ‖b * MandelDim.tau0 w‖ := norm_add_le _ _
          _ ≤ A'' * ‖MandelDim.tau0 w‖ ^ 2 + ‖b‖ * ‖MandelDim.tau0 w‖ := by
              rw [norm_mul]; linarith [hFclose _ htball]
      have h2 : ‖MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ ≤ 2 * ‖MandelDim.tau0 w‖ := by
        rw [norm_mul]; nlinarith [norm_nonneg (MandelDim.tau0 w), hbnd2]
      have h3 : A'' * ‖MandelDim.tau0 w‖ ^ 2 ≤ A'' * ‖MandelDim.tau0 w‖ := by
        have htsq : ‖MandelDim.tau0 w‖ ^ 2 ≤ ‖MandelDim.tau0 w‖ := by
          nlinarith [ht4, norm_nonneg (MandelDim.tau0 w)]
        exact mul_le_mul_of_nonneg_left htsq hA''nn
      have h4 := norm_sub_le (hF (MandelDim.tau0 w) - 1)
        (MandelDim.tau0 w * hF (MandelDim.tau0 w))
      nlinarith [norm_nonneg (MandelDim.tau0 w)]
    have hnum16 : ‖hF (MandelDim.tau0 w) - 1 - MandelDim.tau0 w * hF (MandelDim.tau0 w)‖
        ≤ 1 / 16 := by
      refine le_trans hnum ?_
      have h1 : ‖MandelDim.tau0 w‖ * (‖b‖ + A'' + 2) ≤ δ * (‖b‖ + A'' + 2) :=
        mul_le_mul_of_nonneg_right htnorm (by positivity)
      have h2 : δ * (‖b‖ + A'' + 2) ≤ 1 / 16 := by
        rw [mul_comm]; exact hδK
      linarith
    rw [norm_div]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)‖)]
    have h3 : (1 : ℝ) / 16 ≤ (1 / 8) * ‖1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ := by
      have h := mul_le_mul_of_nonneg_left hden_lb (by norm_num : (0 : ℝ) ≤ (1 / 8))
      linarith
    linarith
  · -- ## derivative estimate
    have hcont : ContinuousAt MandelDim.tau0 w := continuousAt_tau0 hwne
    have hev : ∀ᶠ v in 𝓝 w, MandelDim.tau0 v ∈ Metric.ball (0 : ℂ) r' :=
      hcont.eventually (Metric.isOpen_ball.mem_nhds htball)
    have hdiv_fun : (fun v : ℂ => v / (1 + MandelDim.tau0 v * hF (MandelDim.tau0 v)))
        =ᶠ[𝓝 w] Work.Pert.F0f f₀ := by
      filter_upwards [hev] with v hv
      exact (F0f_eq_div (hFeq (MandelDim.tau0 v) hv)).symm
    have hderiv_eq : deriv (Work.Pert.F0f f₀) w
        = deriv (fun v : ℂ => v / (1 + MandelDim.tau0 v * hF (MandelDim.tau0 v))) w :=
      (Filter.EventuallyEq.deriv_eq hdiv_fun).symm
    have hd_hF : DifferentiableAt ℂ hF (MandelDim.tau0 w) :=
      hFdiff.differentiableAt (Metric.isOpen_ball.mem_nhds htball)
    rw [hderiv_eq, deriv_div_tau0_model hwne hd_hF hden_ne]
    have hnum : ‖deriv hF (MandelDim.tau0 w) - hF (MandelDim.tau0 w) ^ 2‖ ≤ A''' + 4 := by
      have h2 : ‖hF (MandelDim.tau0 w) ^ 2‖ ≤ 4 := by
        rw [norm_pow]; nlinarith [hbnd2, norm_nonneg (hF (MandelDim.tau0 w))]
      have h3 := norm_sub_le (deriv hF (MandelDim.tau0 w)) (hF (MandelDim.tau0 w) ^ 2)
      have h4 : ‖deriv hF (MandelDim.tau0 w)‖ ≤ A''' := hFderiv _ htball
      linarith
    have hkey : (1 + MandelDim.tau0 w ^ 2 *
          (deriv hF (MandelDim.tau0 w) - hF (MandelDim.tau0 w) ^ 2) /
          (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) ^ 2) - 1
        = MandelDim.tau0 w ^ 2 * (deriv hF (MandelDim.tau0 w) - hF (MandelDim.tau0 w) ^ 2) /
          (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) ^ 2 := by ring
    rw [hkey]
    simp only [norm_div, norm_mul, norm_pow, norm_tau0]
    have hden2' : (1 : ℝ) / 4 ≤ ‖1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ ^ 2 := by
      nlinarith [hden_lb, norm_nonneg (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w))]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ ^ 2)]
    have hle1 : (1 / ‖w‖) ^ 2 * ‖deriv hF (MandelDim.tau0 w) - hF (MandelDim.tau0 w) ^ 2‖
        ≤ (1 / ‖w‖) ^ 2 * (A''' + 4) := mul_le_mul_of_nonneg_left hnum (sq_nonneg _)
    have hquot : 0 ≤ 4 * (A''' + 4) / ‖w‖ ^ 2 :=
      div_nonneg (by linarith) (by positivity)
    have hle2 : 4 * (A''' + 4) / ‖w‖ ^ 2 * (1 / 4)
        ≤ 4 * (A''' + 4) / ‖w‖ ^ 2 *
          ‖1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hden2' hquot
    have heq : (1 / ‖w‖) ^ 2 * (A''' + 4) = 4 * (A''' + 4) / ‖w‖ ^ 2 * (1 / 4) := by ring
    linarith

theorem F0f_far_translation {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ Rf : ℝ, 0 < Rf ∧ ∃ Cf : ℝ, 0 < Cf ∧
      (∀ w : ℂ, Rf ≤ ‖w‖ → DifferentiableAt ℂ (Work.Pert.F0f f₀) w ∧
        ‖Work.Pert.F0f f₀ w - (w + 1)‖ ≤ 1 / 8 ∧
        ‖deriv (Work.Pert.F0f f₀) w - 1‖ ≤ Cf / ‖w‖ ^ 2) ∧
      (∀ z : ℂ, Rf ≤ ‖z‖ → ∀ x y : ℂ, ‖x - z‖ ≤ ‖z‖ / 2 → ‖y - z‖ ≤ ‖z‖ / 2 →
        ‖Work.Pert.F0f f₀ x - Work.Pert.F0f f₀ y‖ ≤ (1 + 4 * Cf / ‖z‖ ^ 2) * ‖x - y‖) := by
  obtain ⟨hF, b, r', A'', A''', hr', hA''nn, hA'''nn, hFeq, hFdiff, hFclose, hF0, hFbnd, hFderiv⟩ :=
    exists_model_data hd
  set δ : ℝ := min (min (r' / 2) (1 / 4)) (1 / (16 * (‖b‖ + A'' + 3))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (by linarith) (by norm_num))
      (div_pos one_pos (by linarith [norm_nonneg b, hA''nn]))
  have hδr : δ ≤ r' / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ4 : δ ≤ 1 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδK : (‖b‖ + A'' + 2) * δ ≤ 1 / 16 := by
    have h1 : δ ≤ 1 / (16 * (‖b‖ + A'' + 3)) := min_le_right _ _
    have h2 : (‖b‖ + A'' + 2) * δ ≤ (‖b‖ + A'' + 2) * (1 / (16 * (‖b‖ + A'' + 3))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (‖b‖ + A'' + 2) * (1 / (16 * (‖b‖ + A'' + 3))) ≤ 1 / 16 := by
      rw [mul_one_div, div_le_iff₀ (by linarith [norm_nonneg b, hA''nn])]
      nlinarith [norm_nonneg b, hA''nn]
    linarith
  have hfar := far_pointwise hr' hA''nn hA'''nn hFeq hFdiff hFclose hFbnd hFderiv
    hδpos hδr hδ4 hδK
  refine ⟨2 / δ, by positivity, 4 * (A''' + 4), by linarith, ?_, ?_⟩
  · intro w hw
    refine hfar w (le_trans ?_ hw)
    exact div_le_div_of_nonneg_right (by norm_num) hδpos.le
  · intro z hz x y hx hy
    refine norm_sub_le_of_deriv_close_far (R := 1 / δ) (one_div_pos.mpr hδpos) (by linarith)
      (fun w hw => (hfar w hw).1) (fun w hw => (hfar w hw).2.2) z ?_ x y hx hy
    rw [mul_one_div]
    exact hz

end

end Work.Pert.Ksub2
