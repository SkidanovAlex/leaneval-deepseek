import Submission.Work.Collar3D.Model.Defs

/-!
# Elementary facts about the model disc and circle

`Work.Collar3D.Model.modelDisc_circlePoint`: the boundary of the model flat disc is the model
circle of the plane.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

/-- **The boundary of the model disc is the model circle**: the restriction of the model flat disc
to the boundary circle of `𝔻` is the parametrisation `θ ↦ (cos θ, sin θ, 0)`. -/
theorem modelDisc_circlePoint (θ : ℝ) :
    modelDisc (Work.Smooth.Jordan.circlePoint θ) = planeCircle θ := by
  ext i
  fin_cases i <;>
    simp [modelDisc, planeCircle, WithLp.ofLp_toLp, Work.Smooth.Jordan.circlePoint_coe,
      Complex.exp_ofReal_mul_I, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]

end

end Work.Collar3D
