import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.KinWitnessDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
open Work.SmallBoxA0

/-- Extension of a slot-coordinate integral from the box `abox 1 s` to all of `ℝ³`, for
integrands vanishing off the cube `acube s`:
`∫ x in abox 1 s, F (x 0) = ∫ z : ℝ³, F z` whenever `F z = 0` for `z ∉ acube s`.

HINT.  `Work.SmallBoxA0.integral_abox_one_eq (s := s) (fun x : X 1 => F (x 0))` gives
`∫ x in abox 1 s, F (x 0) = ∫ z in acube s, F z`, and
`MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hF` gives
`∫ z in acube s, F z = ∫ z, F z`.  No measurability or integrability hypothesis is needed. -/
lemma kwBoxExtend {s : ℝ} {F : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ acube s → F z = 0) :
    (∫ x in abox 1 s, F (x 0)) = ∫ z : EuclideanSpace ℝ (Fin 3), F z := by
  rw [integral_abox_one_eq (s := s) (fun x : X 1 => F (x 0))]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hF

end Work.SmallBoxA0
