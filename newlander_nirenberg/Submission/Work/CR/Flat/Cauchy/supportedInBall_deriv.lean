import Mathlib
import Submission.Work.CR.Flat.Cauchy

namespace Work.CR.Flat.Cauchy

open Set Metric

/-- `∂_z f` is continuous as soon as `f` is `C¹`. -/
lemma continuous_dzC {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dzC f) := by
  have h1 : Continuous fun z : ℂ => fderiv ℝ f z 1 :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h2 : Continuous fun z : ℂ => fderiv ℝ f z Complex.I :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  unfold dzC
  exact continuous_const.mul (h1.sub (continuous_const.mul h2))

/-- `∂_z f` vanishes strictly outside the support ball. -/
lemma dzC_eq_zero_of_lt {R : ℝ} {f : ℂ → ℂ} (hfsupp : SupportedInBall R f)
    {ζ : ℂ} (hζ : R < ‖ζ‖) : dzC f ζ = 0 := by
  have hopen : IsOpen {x : ℂ | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hf0 : f =ᶠ[nhds ζ] (fun _ : ℂ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hζ] with x hx
    exact hfsupp x (le_of_lt hx)
  have h1 : HasFDerivAt f (0 : ℂ →L[ℝ] ℂ) ζ :=
    (hasFDerivAt_const (0 : ℂ) ζ).congr_of_eventuallyEq hf0
  simp [dzC, h1.fderiv]

/-- The closure of the open exterior of the disc of radius `R` is the closed
exterior. -/
lemma closure_setOf_lt_norm (R : ℝ) :
    closure {z : ℂ | R < ‖z‖} = {z : ℂ | R ≤ ‖z‖} := by
  have h1 : {z : ℂ | R < ‖z‖} = (Metric.closedBall (0 : ℂ) R)ᶜ := by
    ext z; simp [Metric.mem_closedBall, dist_eq_norm, not_le]
  rw [h1, closure_compl, interior_closedBall']
  ext z; simp [Metric.mem_ball, dist_eq_norm, not_lt]

/-- The `z`-derivative of a `C¹` function supported in the closed disc of
radius `R` is again supported in that disc. -/
theorem supportedInBall_deriv {R : ℝ} {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (h : SupportedInBall R f) : SupportedInBall R (fun z => dzC f z) := by
  intro z hz
  have hcont : Continuous (dzC f) := continuous_dzC hf
  have hclosed : IsClosed {w : ℂ | dzC f w = 0} := isClosed_eq hcont continuous_const
  have hcl : closure {w : ℂ | R < ‖w‖} ⊆ {w : ℂ | dzC f w = 0} :=
    hclosed.closure_subset_iff.mpr (fun w hw => dzC_eq_zero_of_lt h hw)
  exact hcl (by rw [closure_setOf_lt_norm R]; exact hz)

end Work.CR.Flat.Cauchy
