import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! A copy of `v2_contDiffOn_two_integral_Itheta` under a namespace-local name, used by the
copy `Slots.v2_velPert` of the perturbation producer. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

theorem v2_paramC2 {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {C : ℝ}
    (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ C ∧ |Work.Spaces.Dz F z θ| ≤ C ∧ |Work.Spaces.DzIter 2 F z θ| ≤ C) :
    ContDiffOn ℝ 2 (fun z => ∫ θ in Work.Spaces.Iθ, F z θ * φ θ) (Set.Ioi 0) :=
  Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta hφ hF hb

end Work.FTS_RegExport.RXT.Slots
