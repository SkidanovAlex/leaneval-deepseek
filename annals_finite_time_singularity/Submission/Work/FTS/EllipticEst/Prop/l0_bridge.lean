import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-- **The weak class `TT.EllWeakPos` is (a datum of) the a.e. class `H2W.Ae.AeData`.**

The only difference between the two classes is the two moment conditions: `EllWeakPos` demands
`F_*F z = 0` and `F_*Ψ z = 0` for every `z > 0` (pointwise), while `AeData` demands the same
only almost everywhere in `z`.  The pointwise conditions imply the a.e. ones, and every other
field of `AeData α Ψ F` is a field of `EllWeakPos α 0 F Ψ` up to the order of the two functions
(the `α`-bounds are the hypotheses `0 < α`, `α ≤ 1/4` supplied by the caller). -/
theorem aeData_of_ellWeakPos {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F := by
  rcases h with ⟨heq, hzero, hpi, horthF, horthPsi, hsmooth, hmemF, hmemA, hmemB, _hmemC⟩
  refine ⟨hα, hα4, heq, hzero, hpi, hsmooth, hmemF, hmemA, hmemB, ?_, ?_⟩
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact horthPsi z hz
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact horthF z hz

end Work.FTS.EllipticEst.Prop
