import Submission.Work.Smooth.Jordan.Index

/-!
# The standard circle

The positively oriented unit circle `t ↦ e^{it}` as a smooth closed curve, with trace the unit
circle `Metric.sphere (0 : ℂ) 1`.  This is the model instance of the separation and index theory of
this chapter: for it every statement of the theory is proved unconditionally.
-/

open Set
open Classical

namespace Work.Smooth.Jordan

noncomputable section

/-- The standard positively oriented unit circle `t ↦ e^{it}`, as a `C¹` closed curve. -/
def unitCircle : SmoothPlaneCurve where
  γ := fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)
  cont := by fun_prop
  periodic := by
    intro t
    change Complex.exp (((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((t : ℂ) * Complex.I)
    rw [show ((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I
        = (t : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I from by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  contDiff := by
    have h1 : ContDiff ℝ 1 (fun t : ℝ => ((t : ℂ) * Complex.I)) :=
      (Complex.ofRealCLM.contDiff.mul contDiff_const)
    exact Complex.contDiff_exp.comp h1

@[simp] theorem unitCircle_apply (t : ℝ) :
    unitCircle.γ t = Complex.exp ((t : ℂ) * Complex.I) := rfl

/-- The trace of the standard circle is the unit circle of `ℂ`. -/
theorem unitCircle_trace : unitCircle.toPlaneCurve.trace = Metric.sphere (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simpa [Metric.mem_sphere] using Complex.norm_exp_ofReal_mul_I t
  · intro hz
    have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
    obtain ⟨θ, hθ⟩ :=
      exists_circlePoint_eq ⟨z, by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_eq hz1⟩ hz1
    refine ⟨θ, ?_⟩
    change Complex.exp ((θ : ℂ) * Complex.I) = z
    rw [← circlePoint_coe, hθ]

end

end Work.Smooth.Jordan
