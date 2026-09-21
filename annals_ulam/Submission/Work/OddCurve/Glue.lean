import Submission.Work.OddCurve.Defs
import Submission.Work.OddVolterra.Defs

/-!
# Glue with the Volterra chapter

The two moment integrals of this chapter are *definitionally* the integrals of
`Work.OddVolterra` (`momentF`, `momentH`): both are `∫ t in (-x s)..(y s)` of the same integrand
(`rad = psi` and the same exponents).  These two lemmas make the coincidence available for
rewriting, so that a bridge proved in the vocabulary of `Work.OddVolterra` can be transported.
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

lemma momentA_eq_momentF (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) :
    momentA n h x y f s = Work.OddVolterra.momentF n h x y f s := rfl

lemma momentB_eq_momentH (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) :
    momentB n h x y f s = Work.OddVolterra.momentH n h x y f s := rfl

lemma rad_eq_psi (h f : ℝ → ℝ) (s t : ℝ) :
    rad h f s t = Work.OddVolterra.psi h f s t := rfl

lemma refConst_eq_oddSemicircleMomentConstant (n : ℕ) :
    refConst n = Commons.Geometry.Ulam.oddSemicircleMomentConstant n := rfl

end

end Work.OddCurve
