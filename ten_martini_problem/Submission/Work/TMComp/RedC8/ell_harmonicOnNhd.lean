import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.EllDerivDefs
import Submission.Work.TMComp.Kotani.mderiv_bound

/-!
# Harmonicity of the averaged log-modulus `ℓ` on the upper half plane

`ℓ(E) = ∫₀¹ log ‖m(E,y)‖ dy` is the real part of the holomorphic function
`Φ(E) = ∫₀¹ log m(E,y) dy` (complex logarithm), because `m` takes its values in the upper half
plane, where `Re log = log ‖·‖`.  Holomorphy of `Φ` is differentiation under the integral sign:
the `E`-derivative of the integrand is the logarithmic derivative
`R(E,y) = ∂_E m(E,y) / m(E,y) = Rfun α lam E y`, which is bounded on a small ball around `E₀`,
uniformly in the phase, by the Cauchy estimate `mderiv_bound_ball`, and `‖m(E,y)‖` is bounded
below by `min (Im E₀/2) 1` there.  Harmonicity follows from `AnalyticAt.harmonicAt_re`.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMComp.RedC8

open Work.TMComp.Kotani

namespace EllHarm

/-- On the upper half plane the values of `mfun` lie in the slit plane (they have positive
imaginary part). -/
theorem mfun_mem_slitPlane (α lam : ℝ) {z : ℂ} (hz : 0 < z.im) (y : ℝ) :
    mfun α lam z y ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt (MfunProbs.mfun_im_pos α lam hz y)))

/-- The phasewise integrand `y ↦ log (m(E,y))` is continuous for `0 < Im E`. -/
theorem continuous_clog_mfun_phase (α lam : ℝ) {z : ℂ} (hz : 0 < z.im) :
    Continuous (fun y : ℝ => Complex.log (mfun α lam z y)) :=
  (continuous_mfun_phase α lam hz).clog fun y => mfun_mem_slitPlane α lam hz y

/-- The logarithmic derivative `Rfun` is measurable in the phase. -/
theorem measurable_Rfun (α lam : ℝ) {z : ℂ} (hz : 0 < z.im) :
    Measurable (fun y : ℝ => Rfun α lam z y) :=
  (measurable_mderiv α lam z hz).div (continuous_mfun_phase α lam hz).measurable

/-- **Chain rule in the energy.** For `0 < Im z` the derivative of `E ↦ log (m(E,y))` at `z`
is the logarithmic derivative `Rfun α lam z y`. -/
theorem hasDerivAt_clog_mfun (α lam : ℝ) {z : ℂ} (hz : 0 < z.im) (y : ℝ) :
    HasDerivAt (fun E : ℂ => Complex.log (mfun α lam E y)) (Rfun α lam z y) z := by
  have hg : HasDerivAt (fun E : ℂ => mfun α lam E y) (mderiv α lam z y) z :=
    ((MfunProbs.mfun_differentiableOn α lam y).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)).hasDerivAt
  exact hg.clog (mfun_mem_slitPlane α lam hz y)

/-- `ℓ` is the real part of the complex interval integral of `log (m(·,y))`. -/
theorem ell_eq_re_clog_integral (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    ell α lam E = (∫ y in (0 : ℝ)..1, Complex.log (mfun α lam E y)).re := by
  have hf : IntervalIntegrable (fun y : ℝ => Complex.log (mfun α lam E y)) volume 0 1 :=
    (continuous_clog_mfun_phase α lam hE).intervalIntegrable 0 1
  have hre : (∫ y in (0 : ℝ)..1, Complex.log (mfun α lam E y)).re
      = ∫ y in (0 : ℝ)..1, (Complex.log (mfun α lam E y)).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hf).symm
  rw [ell, hre]
  exact intervalIntegral.integral_congr fun y _ => (Complex.log_re _).symm

/-- **Cauchy estimate on a ball.** The energy-derivative of the `m`-function is bounded on the
complex ball of radius `Im E₀ / 4` around `E₀`, uniformly in the phase. -/
theorem mderiv_bound_ball (α lam : ℝ) (E₀ : ℂ) (hE₀ : 0 < E₀.im) :
    ∃ C : ℝ, ∀ z ∈ Metric.ball E₀ (E₀.im / 4), ∀ y : ℝ,
      ‖mderiv α lam z y‖ ≤ C := by
  refine ⟨max 1 (‖E₀‖ + E₀.im / 2 + 2 * |lam| + 1 / min (E₀.im / 4) 1) / (E₀.im / 4), ?_⟩
  have hρ : 0 < E₀.im / 4 := by linarith
  have hh : 0 < min (E₀.im / 4) 1 := lt_min hρ one_pos
  have h1 : min (E₀.im / 4) 1 ≤ 1 := min_le_right _ _
  have hmin4 : min (E₀.im / 4) 1 ≤ E₀.im / 4 := min_le_left _ _
  intro z hz y
  have hznorm : ‖z - E₀‖ < E₀.im / 4 := by
    have h := Metric.mem_ball.mp hz
    rwa [dist_eq_norm] at h
  have hz3 : 3 * E₀.im / 4 < z.im := by
    have h2 : |z.im - E₀.im| ≤ ‖z - E₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - E₀)
    have h3 := (abs_lt.mp (lt_of_le_of_lt h2 hznorm)).1
    linarith
  have hzim : min (E₀.im / 4) 1 ≤ z.im :=
    le_trans hmin4 (by linarith)
  have hsub : Metric.closedBall z (E₀.im / 4) ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have hwd : dist w z ≤ E₀.im / 4 := Metric.mem_closedBall.mp hw
    have h2 : |w.im - z.im| ≤ ‖w - z‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
    have h3 : ‖w - z‖ ≤ E₀.im / 4 := by rwa [dist_eq_norm] at hwd
    have h4 := (abs_le.mp (le_trans h2 h3)).1
    show 0 < w.im
    linarith
  have hdc : DiffContOnCl ℂ (fun w : ℂ => mfun α lam w y) (Metric.ball z (E₀.im / 4)) :=
    (MfunProbs.mfun_differentiableOn α lam y).diffContOnCl_ball hsub
  have hC : ∀ w ∈ Metric.sphere z (E₀.im / 4),
      ‖mfun α lam w y‖ ≤ max 1 (‖E₀‖ + E₀.im / 2 + 2 * |lam| + 1 / min (E₀.im / 4) 1) := by
    intro w hw
    have hwd : ‖w - z‖ = E₀.im / 4 := by
      have h := Metric.mem_sphere.mp hw
      rwa [dist_eq_norm] at h
    have hwim : min (E₀.im / 4) 1 ≤ w.im := by
      have h2 : |w.im - z.im| ≤ ‖w - z‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
      have h3 := (abs_le.mp (le_trans h2 (le_of_eq hwd))).1
      exact le_trans hmin4 (by linarith)
    have hwnorm : ‖w‖ ≤ ‖E₀‖ + E₀.im / 2 := by
      have h3 : ‖w‖ ≤ ‖z‖ + E₀.im / 4 := by
        calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
          _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
          _ = ‖z‖ + E₀.im / 4 := by rw [hwd]
      have h4 : ‖z‖ ≤ ‖E₀‖ + E₀.im / 4 := by
        calc ‖z‖ = ‖E₀ + (z - E₀)‖ := by ring_nf
          _ ≤ ‖E₀‖ + ‖z - E₀‖ := norm_add_le _ _
          _ ≤ ‖E₀‖ + E₀.im / 4 := by linarith [le_of_lt hznorm]
      linarith
    calc ‖mfun α lam w y‖ ≤ max 1 (‖w‖ + 2 * |lam| + 1 / min (E₀.im / 4) 1) :=
          mfun_norm_le α lam hh h1 hwim y
      _ ≤ max 1 (‖E₀‖ + E₀.im / 2 + 2 * |lam| + 1 / min (E₀.im / 4) 1) := by
          apply max_le_max_left
          linarith
  have hbd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := fun w : ℂ => mfun α lam w y) (c := z) (R := E₀.im / 4)
    (C := max 1 (‖E₀‖ + E₀.im / 2 + 2 * |lam| + 1 / min (E₀.im / 4) 1)) hρ hdc hC
  calc ‖mderiv α lam z y‖ = ‖deriv (fun w : ℂ => mfun α lam w y) z‖ := rfl
    _ ≤ max 1 (‖E₀‖ + E₀.im / 2 + 2 * |lam| + 1 / min (E₀.im / 4) 1) / (E₀.im / 4) := hbd

end EllHarm

/-- **Harmonicity of `ℓ` on the upper half plane.** -/
theorem ell_harmonicOnNhd (α lam : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun E : ℂ => Work.TMComp.Kotani.ell α lam E)
      {z : ℂ | 0 < z.im} := by
  have hderiv : DifferentiableOn ℂ
      (fun E : ℂ => ∫ y in (0 : ℝ)..1, Complex.log (mfun α lam E y))
      {z : ℂ | 0 < z.im} := by
    intro z₀ hz₀
    have hz₀' : 0 < z₀.im := hz₀
    obtain ⟨C, hC⟩ := EllHarm.mderiv_bound_ball α lam z₀ hz₀'
    have hρ : 0 < z₀.im / 4 := by linarith
    have h0pos : 0 < min (z₀.im / 2) 1 := lt_min (by linarith) one_pos
    have h0le1 : min (z₀.im / 2) 1 ≤ 1 := min_le_right _ _
    have himlow : ∀ z ∈ Metric.ball z₀ (z₀.im / 4), min (z₀.im / 2) 1 ≤ z.im := by
      intro z hz
      have hzd : ‖z - z₀‖ < z₀.im / 4 := by
        have h := Metric.mem_ball.mp hz
        rwa [dist_eq_norm] at h
      have h2 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
      have h3 := (abs_lt.mp (lt_of_le_of_lt h2 hzd)).1
      exact le_trans (min_le_left _ _) (by linarith)
    have hmfun_low : ∀ z ∈ Metric.ball z₀ (z₀.im / 4), ∀ y : ℝ,
        min (z₀.im / 2) 1 ≤ ‖mfun α lam z y‖ := by
      intro z hz y
      exact le_trans (mfun_im_ge α lam h0pos h0le1 (himlow z hz) y) (Complex.im_le_norm _)
    have hRbound : ∀ z ∈ Metric.ball z₀ (z₀.im / 4), ∀ y : ℝ,
        ‖Rfun α lam z y‖ ≤ C / min (z₀.im / 2) 1 := by
      intro z hz y
      have h1 : ‖Rfun α lam z y‖ = ‖mderiv α lam z y‖ / ‖mfun α lam z y‖ := by
        rw [Rfun, norm_div]
      rw [h1]
      exact div_le_div₀ (le_trans (norm_nonneg _) (hC z hz y)) (hC z hz y) h0pos
        (hmfun_low z hz y)
    have hFmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable
        (fun y : ℝ => Complex.log (mfun α lam z y)) (volume.restrict (uIoc 0 1)) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀'] with z hz
      exact (EllHarm.continuous_clog_mfun_phase α lam hz).aestronglyMeasurable
    have hFint : IntervalIntegrable (fun y : ℝ => Complex.log (mfun α lam z₀ y)) volume 0 1 :=
      (EllHarm.continuous_clog_mfun_phase α lam hz₀').intervalIntegrable 0 1
    have hF'meas : AEStronglyMeasurable (fun y : ℝ => Rfun α lam z₀ y)
        (volume.restrict (uIoc 0 1)) :=
      (EllHarm.measurable_Rfun α lam hz₀').aestronglyMeasurable
    have hbound : ∀ᵐ y ∂volume, y ∈ uIoc 0 1 →
        ∀ z ∈ Metric.ball z₀ (z₀.im / 4), ‖Rfun α lam z y‖ ≤ C / min (z₀.im / 2) 1 :=
      Filter.Eventually.of_forall fun y _ z hz => hRbound z hz y
    have hboundint : IntervalIntegrable (fun _ : ℝ => C / min (z₀.im / 2) 1) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hdiff : ∀ᵐ y ∂volume, y ∈ uIoc 0 1 → ∀ z ∈ Metric.ball z₀ (z₀.im / 4),
        HasDerivAt (fun z : ℂ => Complex.log (mfun α lam z y)) (Rfun α lam z y) z :=
      Filter.Eventually.of_forall fun y _ z hz =>
        EllHarm.hasDerivAt_clog_mfun α lam (lt_of_lt_of_le h0pos (himlow z hz)) y
    have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (𝕜 := ℂ)
      (F := fun (z : ℂ) (y : ℝ) => Complex.log (mfun α lam z y))
      (F' := fun (z : ℂ) (y : ℝ) => Rfun α lam z y)
      (x₀ := z₀) (s := Metric.ball z₀ (z₀.im / 4)) (a := 0) (b := 1)
      (bound := fun _ => C / min (z₀.im / 2) 1)
      (Metric.ball_mem_nhds z₀ hρ) hFmeas hFint hF'meas hbound hboundint hdiff
    exact (hmain.2.differentiableAt).differentiableWithinAt
  intro E₀ hE₀
  have hE₀' : 0 < E₀.im := hE₀
  have hanalytic : AnalyticAt ℂ
      (fun E : ℂ => ∫ y in (0 : ℝ)..1, Complex.log (mfun α lam E y)) E₀ :=
    hderiv.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im) E₀ hE₀
  have hharm : InnerProductSpace.HarmonicAt
      (fun E : ℂ => (∫ y in (0 : ℝ)..1, Complex.log (mfun α lam E y)).re) E₀ :=
    hanalytic.harmonicAt_re
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hharm
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hE₀'] with E hE
  exact (EllHarm.ell_eq_re_clog_integral α lam E hE).symm

end Work.TMComp.RedC8
