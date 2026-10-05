import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.Helpers
import Submission.Work.RPV.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real

/-- A `C^∞` embedding of the circle into `ℂ`, read through the standard parametrisation
`t ↦ e^{it}` of the circle, is a smooth loop: `C^∞`, `2π`-periodic, injective modulo `2π`
and immersed.  The four fields of `IsSmoothLoop` are:

* *smoothness*: `Circle.exp` is smooth (`contMDiff_circleExp`) and `γ` is smooth, so the
  composite is `ContMDiff`; `contMDiff_iff_contDiff` converts this to `ContDiff ℝ ∞`;
* *periodicity*: `Circle.periodic_exp`;
* *injectivity mod `2π`*: `γ` is injective (`IsSmoothEmbedding.isEmbedding`) and
  `Circle.exp_eq_exp` computes the kernel of `Circle.exp` as `2πℤ`;
* *immersion*: `curve_deriv_ne_zero_C`. -/
theorem isSmoothLoop_of_isSmoothJordan (γ : Circle → ℂ) (hγ : Work.RPV.IsSmoothJordan γ) :
    Work.RPB1a.IsSmoothLoop (fun t : ℝ => γ (Circle.exp t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact contMDiff_iff_contDiff.mp (hγ.contMDiff.comp contMDiff_circleExp)
  · intro t
    exact congrArg γ (Circle.periodic_exp t)
  · intro t t' h
    have h2 : Circle.exp t = Circle.exp t' := hγ.isEmbedding.injective h
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h2
    exact ⟨-m, by push_cast at hm ⊢; linarith⟩
  · intro t
    exact curve_deriv_ne_zero_C γ hγ t

end Work.RPB1a
