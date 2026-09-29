import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.EllDerivDefs
import Submission.Work.TMComp.Kotani.mderiv_bound
import Submission.Work.TMComp.Kotani.Rfun_eq_defect

/-!
# C8 (Kotani theory): the derivative of the averaged log-modulus `ℓ`

This file proves `Work.TMComp.Kotani.hasDerivAt_ell`, step (L5) of the Kotani computation:
for `ε > 0` the vertical derivative of
`t ↦ ℓ(E₀ + i t) = ∫₀¹ log ‖m(E₀ + i t, y)‖ dy`
at `t = ε` equals `∫₀¹ Im(-1/defect(E₀ + i ε, y)) dy`.

The proof has three parts.

* **Differentiation under the integral.**  For `t` in a neighbourhood of `ε`, the integrand
  `t ↦ log ‖m(E₀ + i t, y)‖` has derivative `-Im R(E₀ + i t, y)` (the chain rule along the
  vertical direction, `hasDerivAt_log_norm_mfun`), and this derivative is bounded uniformly in
  `y` on the strip `ε/2 < t < 2ε` (via the Cauchy estimate `mderiv_bound`).  Hence
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` gives
  `ℓ'(E₀ + i ε) = ∫₀¹ -Im R(E₀ + i ε, y) dy`.

* **The (L5) identity.**  `Rfun_eq_defect` writes
  `R(E, y) = 1/defect(E, y+α) - m'(E,y+α)/defect(E,y+α) + m'(E,y)/defect(E,y)`.

* **The coboundary integrates to zero.**  Both `y ↦ 1/defect(E,y)` and `y ↦ m'(E,y)/defect(E,y)`
  are `1`-periodic in `y`, so integrating the identity over `(0,1)` gives
  `∫₀¹ Im R = ∫₀¹ Im(1/defect)`, whence `∫₀¹ -Im R = ∫₀¹ Im(-1/defect)`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani
open Work.TMContract

theorem hasDerivAt_ell (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) :
    HasDerivAt (fun t : ℝ => Work.TMComp.Kotani.ell α lam ((E₀ : ℂ) + (t : ℂ) * Complex.I))
      (∫ y in (0 : ℝ)..1,
        (-1 / Work.TMComp.Kotani.defect α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y).im) ε := by
  set E₁ : ℂ := (E₀ : ℂ) + (ε : ℂ) * Complex.I with hE₁def
  have hE₁im : E₁.im = ε := by rw [hE₁def]; simp
  have hE₁ : 0 < E₁.im := by rw [hE₁im]; exact hε
  obtain ⟨C, hC⟩ := mderiv_bound α lam E₀ ε hε
  have hminε2 : 0 < min (ε/2) 1 := lt_min (by linarith) one_pos
  have hminε : 0 < min ε 1 := lt_min hε one_pos
  have hRnet : ∀ u : ℝ, ε/2 < u → u < 2*ε → ∀ y : ℝ,
      ‖(-(Rfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y).im)‖ ≤ C / min (ε/2) 1 := by
    intro u hu1 hu2 y
    have hu0 : 0 < u := lt_trans (by linarith) hu1
    have hEu : ((E₀:ℂ)+(u:ℂ)*Complex.I).im = u := by simp
    have hlow : min (ε/2) 1 ≤ (mfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y).im := by
      have h := mfun_im_ge α lam (E := ((E₀:ℂ)+(u:ℂ)*Complex.I)) (h := min u 1)
        (lt_min hu0 one_pos) (min_le_right _ _) (by rw [hEu]; exact min_le_left _ _) y
      have h2 : min (ε/2) 1 ≤ min u 1 :=
        le_min (le_trans (min_le_left _ _) (by linarith)) (min_le_right _ _)
      linarith
    have hnorm : min (ε/2) 1 ≤ ‖mfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y‖ :=
      le_trans hlow (Complex.im_le_norm _)
    have hC' : ‖mderiv α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y‖ ≤ C := hC u hu1 hu2 y
    have hdiv : ‖Rfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y‖ ≤ C / min (ε/2) 1 := by
      rw [Rfun, norm_div]
      exact div_le_div₀ (le_trans (norm_nonneg _) hC') hC' hminε2 hnorm
    calc ‖(-(Rfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y).im)‖
        = |(Rfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y).im| := by rw [Real.norm_eq_abs, abs_neg]
      _ ≤ ‖Rfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y‖ := Complex.abs_im_le_norm _
      _ ≤ C / min (ε/2) 1 := hdiv
  have hmain : HasDerivAt (fun t : ℝ => ell α lam ((E₀:ℂ)+(t:ℂ)*Complex.I))
      (∫ y in (0:ℝ)..1, (-(Rfun α lam E₁ y).im)) ε := by
    have hs : Set.Ioo (ε/2) (2*ε) ∈ 𝓝 ε := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hFmeas : ∀ᶠ u : ℝ in 𝓝 ε, AEStronglyMeasurable
        (fun y : ℝ => Real.log ‖mfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y‖)
        (volume.restrict (uIoc 0 1)) := by
      filter_upwards [hs] with u hu
      have hu0 : 0 < u := lt_trans (by linarith) hu.1
      have hEu : 0 < ((E₀:ℂ)+(u:ℂ)*Complex.I).im := by simpa using hu0
      have hcont : Continuous (fun y : ℝ => Real.log ‖mfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y‖) :=
        (continuous_norm.comp (continuous_mfun_phase α lam hEu)).log
          (fun y => norm_ne_zero_iff.mpr
            (ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hEu y))))
      exact hcont.aestronglyMeasurable
    have hFint : IntervalIntegrable (fun y : ℝ => Real.log ‖mfun α lam E₁ y‖) volume 0 1 := by
      have hcont : Continuous (fun y : ℝ => Real.log ‖mfun α lam E₁ y‖) :=
        (continuous_norm.comp (continuous_mfun_phase α lam hE₁)).log
          (fun y => norm_ne_zero_iff.mpr
            (ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hE₁ y))))
      exact hcont.intervalIntegrable 0 1
    have hF'meas : AEStronglyMeasurable (fun y : ℝ => (-(Rfun α lam E₁ y).im))
        (volume.restrict (uIoc 0 1)) := (measurable_Rfun_im α lam E₁ hE₁).neg.aestronglyMeasurable
    have hbound : ∀ᵐ t ∂volume, t ∈ uIoc 0 1 → ∀ u ∈ Set.Ioo (ε/2) (2*ε),
        ‖(-(Rfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) t).im)‖ ≤ C / min (ε/2) 1 :=
      Filter.Eventually.of_forall (fun t _ u hu => hRnet u hu.1 hu.2 t)
    have hboundint : IntervalIntegrable (fun _ : ℝ => C / min (ε/2) 1) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hdiff : ∀ᵐ t ∂volume, t ∈ uIoc 0 1 → ∀ u ∈ Set.Ioo (ε/2) (2*ε),
        HasDerivAt (fun u : ℝ => Real.log ‖mfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) t‖)
          (-(Rfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) t).im) u :=
      Filter.Eventually.of_forall (fun t _ u hu =>
        hasDerivAt_log_norm_mfun α lam E₀ (by linarith [hu.1]) t)
    have h := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (𝕜 := ℝ)
      (F := fun (u : ℝ) (y:ℝ) => Real.log ‖mfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y‖)
      (F' := fun (u : ℝ) (y:ℝ) => (-(Rfun α lam ((E₀:ℂ)+(u:ℂ)*Complex.I) y).im))
      (x₀ := ε) (s := Set.Ioo (ε/2) (2*ε)) (a := 0) (b := 1)
      (bound := fun _ => C / min (ε/2) 1) hs hFmeas hFint hF'meas hbound hboundint hdiff).2
    simpa [ell, hE₁def] using h
  have hIntEq : ∫ y in (0:ℝ)..1, (Rfun α lam E₁ y).im
      = ∫ y in (0:ℝ)..1, (1/defect α lam E₁ y).im := by
    have hcont_def : Continuous (fun y : ℝ => 1/defect α lam E₁ (y+α)) :=
      continuous_const.div (continuous_defect_phase α lam hE₁ |>.comp (continuous_id.add continuous_const))
        (fun y => defect_ne_zero α lam hE₁ (y+α))
    have hInt_gα : IntervalIntegrable (fun y : ℝ => (1/defect α lam E₁ (y+α)).im) volume 0 1 :=
      (Complex.continuous_im.comp hcont_def).intervalIntegrable 0 1
    have hHbound : ∀ y : ℝ, ‖(Hfun α lam E₁ y).im‖ ≤ C / min ε 1 := by
      intro y
      have hC' : ‖mderiv α lam E₁ y‖ ≤ C := by
        have hh := hC ε (by linarith) (by linarith) y
        rwa [← hE₁def] at hh
      have hlow : min ε 1 ≤ (defect α lam E₁ y).im :=
        le_trans (mfun_im_ge α lam (E := E₁) (h := min ε 1) hminε (min_le_right _ _)
          (by rw [hE₁im]; exact min_le_left ε 1) y) (mfun_im_le_defect_im α lam hE₁ y)
      have hnorm : min ε 1 ≤ ‖defect α lam E₁ y‖ := le_trans hlow (Complex.im_le_norm _)
      have hdiv : ‖Hfun α lam E₁ y‖ ≤ C / min ε 1 := by
        rw [Hfun, norm_div]
        exact div_le_div₀ (le_trans (norm_nonneg _) hC') hC' hminε hnorm
      exact le_trans (Complex.abs_im_le_norm _) hdiv
    have hInt_h : IntervalIntegrable (fun y : ℝ => (Hfun α lam E₁ y).im) volume 0 1 := by
      rw [intervalIntegrable_iff]
      refine IntegrableOn.of_bound (by simp)
        (measurable_Hfun_im α lam E₁ hE₁).aestronglyMeasurable (C / min ε 1) ?_
      exact Filter.Eventually.of_forall hHbound
    have hInt_hα : IntervalIntegrable (fun y : ℝ => (Hfun α lam E₁ (y+α)).im) volume 0 1 := by
      rw [intervalIntegrable_iff]
      refine IntegrableOn.of_bound (by simp)
        ((measurable_Hfun_im α lam E₁ hE₁).comp
          (measurable_id.add measurable_const)).aestronglyMeasurable (C / min ε 1) ?_
      exact Filter.Eventually.of_forall (fun y => hHbound (y+α))
    have hpt : ∀ y : ℝ, (Rfun α lam E₁ y).im
        = (1/defect α lam E₁ (y+α)).im - (Hfun α lam E₁ (y+α)).im + (Hfun α lam E₁ y).im := by
      intro y
      rw [Rfun_eq_defect α lam hE₁ y, Hfun, Hfun]
      simp only [Complex.add_im, Complex.sub_im]
    have hper_g : Function.Periodic (fun y : ℝ => (1/defect α lam E₁ y).im) 1 := by
      intro y; simp only [defect_period]
    have hper_h : Function.Periodic (fun y : ℝ => (Hfun α lam E₁ y).im) 1 := by
      intro y; simp only [Hfun_period]
    have hshift_g : ∫ y in (0:ℝ)..1, (1/defect α lam E₁ (y+α)).im
        = ∫ y in (0:ℝ)..1, (1/defect α lam E₁ y).im := by
      rw [intervalIntegral.integral_comp_add_right (fun y => (1/defect α lam E₁ y).im) α]
      rw [show (0:ℝ) + α = α by ring, show (1:ℝ) + α = α + 1 by ring]
      simpa using hper_g.intervalIntegral_add_eq α 0
    have hshift_h : ∫ y in (0:ℝ)..1, (Hfun α lam E₁ (y+α)).im
        = ∫ y in (0:ℝ)..1, (Hfun α lam E₁ y).im := by
      rw [intervalIntegral.integral_comp_add_right (fun y => (Hfun α lam E₁ y).im) α]
      rw [show (0:ℝ) + α = α by ring, show (1:ℝ) + α = α + 1 by ring]
      simpa using hper_h.intervalIntegral_add_eq α 0
    have e1 : ∫ y in (0:ℝ)..1, (Rfun α lam E₁ y).im
        = ∫ y in (0:ℝ)..1, ((1/defect α lam E₁ (y+α)).im - (Hfun α lam E₁ (y+α)).im
            + (Hfun α lam E₁ y).im) :=
      intervalIntegral.integral_congr (fun y _ => hpt y)
    have e2 : ∫ y in (0:ℝ)..1, ((1/defect α lam E₁ (y+α)).im - (Hfun α lam E₁ (y+α)).im
            + (Hfun α lam E₁ y).im)
        = (∫ y in (0:ℝ)..1, ((1/defect α lam E₁ (y+α)).im - (Hfun α lam E₁ (y+α)).im))
          + ∫ y in (0:ℝ)..1, (Hfun α lam E₁ y).im :=
      intervalIntegral.integral_add (hInt_gα.sub hInt_hα) hInt_h
    have e3 : ∫ y in (0:ℝ)..1, ((1/defect α lam E₁ (y+α)).im - (Hfun α lam E₁ (y+α)).im)
        = (∫ y in (0:ℝ)..1, (1/defect α lam E₁ (y+α)).im)
          - ∫ y in (0:ℝ)..1, (Hfun α lam E₁ (y+α)).im :=
      intervalIntegral.integral_sub hInt_gα hInt_hα
    rw [e1, e2, e3, hshift_g, hshift_h]
    ring
  have hneg1 : ∫ y in (0:ℝ)..1, (-(Rfun α lam E₁ y).im)
      = -∫ y in (0:ℝ)..1, (Rfun α lam E₁ y).im := intervalIntegral.integral_neg
  have hneg2 : ∫ y in (0:ℝ)..1, ((-1/defect α lam E₁ y).im)
      = -∫ y in (0:ℝ)..1, (1/defect α lam E₁ y).im := by
    have hfun : (fun y : ℝ => ((-1/defect α lam E₁ y).im))
        = (fun y : ℝ => -((1/defect α lam E₁ y).im)) := by
      funext y; simp [Complex.neg_im, neg_div]
    rw [hfun]
    exact intervalIntegral.integral_neg
  have key : (∫ y in (0:ℝ)..1, (-(Rfun α lam E₁ y).im))
      = (∫ y in (0:ℝ)..1, ((-1/defect α lam E₁ y).im)) := by
    rw [hneg1, hneg2, hIntEq]
  convert hmain using 1
  exact key.symm


end Work.TMComp.Kotani
