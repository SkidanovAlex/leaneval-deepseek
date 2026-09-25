/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Pompeiu's formula in the plane

`Work.CR.Flat.Cauchy.pompeiu`: for a `C¹` function `f` vanishing outside the disc of radius `R`
and `‖z‖ < R`, `-π⁻¹ ∫_{‖ζ‖<R} (∂̄f)(ζ)/(ζ - z) dA(ζ) = f z`.

The origin case `z = 0` is `Work.CR.Flat.Cauchy.cauchyGreen_origin` (proved by the polar
coordinate computation).  Here we reduce the general case to it by translating: the shifted
function `w ↦ f (z + w)` has the same `∂̄` and is supported in a disc centred at the origin of
radius `R + ‖z‖ + 1`, so `cauchyGreen_origin` applied to it computes `∫ (∂̄f)(z+w)/w`, which is
`∫ (∂̄f)(ζ)/(ζ-z)` by the translation invariance of Lebesgue measure.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.cauchyGreen_origin

noncomputable section

open scoped NNReal ENNReal Topology
open Filter MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- Translation invariance of `∂̄`: `∂̄(f(· + a)) = (∂̄f)(· + a)`. -/
private lemma dbarC_comp_add (f : ℂ → ℂ) (a ζ : ℂ) (hf : DifferentiableAt ℝ f (a + ζ)) :
    dbarC (fun w => f (a + w)) ζ = dbarC f (a + ζ) := by
  have h1 : HasFDerivAt (fun w : ℂ => a + w) (ContinuousLinearMap.id ℝ ℂ) ζ :=
    (hasFDerivAt_id ζ).const_add a
  have h2 : HasFDerivAt (fun w : ℂ => f (a + w)) (fderiv ℝ f (a + ζ)) ζ := by
    have h := (hf.hasFDerivAt).comp ζ h1
    rwa [ContinuousLinearMap.comp_id] at h
  rw [dbarC, dbarC, h2.fderiv]

/-- `∂̄f` is continuous when `f` is `C¹`. -/
private lemma continuous_dbarC {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dbarC f) := by
  have h : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  unfold dbarC
  fun_prop

/-- Strict form: if `f` vanishes where `R < ‖ζ‖` then `∂̄f` vanishes there, because `f` is
locally `0` on that open set. -/
lemma dbarC_eq_zero_of_lt {R : ℝ} {f : ℂ → ℂ} (hfsupp : SupportedInBall R f) {w : ℂ}
    (hw : R < ‖w‖) : dbarC f w = 0 := by
  have hopen : IsOpen {x : ℂ | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hf0 : f =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hw] with y hy
    exact hfsupp y hy.le
  have h := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) w).congr_of_eventuallyEq hf0
  simp [dbarC, h.fderiv]

/-- Non-strict form: if `f` is `C¹` and vanishes outside the disc of radius `R`, then `∂̄f`
vanishes on the closed disc `‖ζ‖ ≤ R` (continuity of `∂̄f` and the strict form). -/
lemma dbarC_eq_zero_of_supportedInBall {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (hfsupp : SupportedInBall R f) {ζ : ℂ} (hζ : R ≤ ‖ζ‖) :
    dbarC f ζ = 0 := by
  have hcont : Continuous (dbarC f) := continuous_dbarC hf
  have hS : IsClosed {x : ℂ | dbarC f x = 0} := isClosed_eq hcont continuous_const
  have hsub : ∀ x : ℂ, R < ‖x‖ → dbarC f x = 0 := fun x hx => dbarC_eq_zero_of_lt hfsupp hx
  have htend : Tendsto (fun n : ℕ => ζ * ((1 + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 ζ) := by
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h4 : Tendsto (fun n : ℕ => (1 + ((n : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add h2
    have h5 : Tendsto (fun n : ℕ => ((1 + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp h4
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ζ) atTop (𝓝 ζ)).mul h5
  have hmem : ∀ᶠ n : ℕ in atTop,
      ζ * ((1 + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) ∈ {x : ℂ | dbarC f x = 0} := by
    refine Filter.Eventually.of_forall (fun n => ?_)
    apply hsub
    have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le hR hζ
    have hinv : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hprod : 0 < ‖ζ‖ * ((n : ℝ) + 1)⁻¹ := mul_pos hζpos hinv
    nlinarith [hζpos, hinv, hζ, hprod]
  exact (by simpa only [Set.mem_ofPred_eq] using hS.mem_of_tendsto htend hmem)

/-- **Pompeiu's formula** in the plane. -/
theorem pompeiu {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R) (hf : ContDiff ℝ 1 f)
    (hfsupp : SupportedInBall R f) {z : ℂ} (hz : ‖z‖ < R) :
    -((Real.pi : ℂ))⁻¹ * ∫ ζ in Metric.ball 0 R, (dbarC f ζ) / (ζ - z) = f z := by
  have _hz : ‖z‖ < R := hz
  set R' : ℝ := R + ‖z‖ + 1 with hR'def
  have hR'pos : 0 < R' := by rw [hR'def]; positivity
  have hfsupp' : SupportedInBall R' (fun w : ℂ => f (z + w)) := by
    intro w hw
    show f (z + w) = 0
    apply hfsupp
    have h1 : ‖w‖ ≤ ‖z + w‖ + ‖z‖ := by
      have := norm_sub_le (z + w) z
      rwa [add_sub_cancel_left] at this
    rw [hR'def] at hw
    linarith
  have hg : ContDiff ℝ 1 (fun w : ℂ => f (z + w)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have hkey := cauchyGreen_origin hR'pos hg hfsupp'
  -- rewrite `∂̄(f(z+·))` as `(∂̄f)(z+·)`
  have hI : (∫ ζ in Metric.ball 0 R', dbarC (fun w => f (z + w)) ζ / ζ)
      = ∫ w in Metric.ball 0 R', (dbarC f (z + w)) / w := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro w _
    change dbarC (fun w' => f (z + w')) w / w = dbarC f (z + w) / w
    rw [dbarC_comp_add f z w ((hf.differentiable one_ne_zero) (z + w))]
  rw [hI] at hkey
  -- relate the two integrals
  have hint1 : ∫ w in Metric.ball 0 R', (dbarC f (z + w)) / w
      = ∫ w : ℂ, (dbarC f (z + w)) / w := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    have hwR : R' ≤ ‖w‖ := by
      rw [Metric.mem_ball, not_lt] at hw
      simpa [dist_eq_norm] using hw
    have : R < ‖z + w‖ := by
      have h1 : ‖w‖ ≤ ‖z + w‖ + ‖z‖ := by
        have := norm_sub_le (z + w) z
        rwa [add_sub_cancel_left] at this
      rw [hR'def] at hwR
      linarith
    rw [dbarC_eq_zero_of_lt hfsupp this, zero_div]
  have hint2 : ∫ w : ℂ, (dbarC f (z + w)) / w = ∫ ζ : ℂ, (dbarC f ζ) / (ζ - z) := by
    have h := integral_add_left_eq_self (μ := (volume : Measure ℂ))
      (fun ζ : ℂ => (dbarC f ζ) / (ζ - z)) z
    simpa [add_sub_cancel_left] using h
  have hint3 : ∫ ζ : ℂ, (dbarC f ζ) / (ζ - z)
      = ∫ ζ in Metric.ball 0 R, (dbarC f ζ) / (ζ - z) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ζ hζ
    have hζR : R ≤ ‖ζ‖ := by
      rw [Metric.mem_ball, not_lt] at hζ
      simpa [dist_eq_norm] using hζ
    rw [dbarC_eq_zero_of_supportedInBall hR hf hfsupp hζR, zero_div]
  rw [hint1.trans (hint2.trans hint3)] at hkey
  simpa using hkey

end Work.CR.Flat.Cauchy
