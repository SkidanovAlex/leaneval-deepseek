import Mathlib
import Submission.Work.Sweep.Defs

namespace Work.Sweep.SqDist

/-- The squared distance from a fixed point `x` to the curve of a knot is
differentiable, with derivative `2 * ⟪γ t - x, γ' t⟫`. -/
theorem hasDerivAt_sqDist (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (x : LeanEval.KnotTheory.PardonDistortion.R3) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ‖K.curve u - x‖ ^ 2)
      (2 * inner ℝ (K.curve t - x) (deriv K.curve t)) t := by
  have hdiff : HasDerivAt K.curve (deriv K.curve t) t :=
    (K.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hf : HasDerivAt (fun u : ℝ => K.curve u - x) (deriv K.curve t) t :=
    hdiff.sub_const x
  have hinner : HasDerivAt (fun u : ℝ => inner ℝ (K.curve u - x) (K.curve u - x))
      (inner ℝ (K.curve t - x) (deriv K.curve t)
        + inner ℝ (deriv K.curve t) (K.curve t - x)) t :=
    hf.inner ℝ hf
  have hfun : (fun u : ℝ => ‖K.curve u - x‖ ^ 2)
      = fun u : ℝ => inner ℝ (K.curve u - x) (K.curve u - x) := by
    funext u; exact (real_inner_self_eq_norm_sq _).symm
  rw [hfun]
  convert hinner using 1
  rw [real_inner_comm (deriv K.curve t) (K.curve t - x)]
  ring

end Work.Sweep.SqDist
