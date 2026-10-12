import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.BoseBoxFock.continuousSetIntegralCompactGenMulV2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem continuous_setIntegral_compact_gen_mul
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureTheory.MeasureSpace G]
    [BorelSpace G]
    [MeasureTheory.IsFiniteMeasureOnCompacts (MeasureTheory.volume : MeasureTheory.Measure G)]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {k : Set G} (hk : IsCompact k) {a : G → ℂ} {Ca : ℝ}
    (ha : MeasureTheory.AEStronglyMeasurable a
      ((MeasureTheory.volume : MeasureTheory.Measure G).restrict k))
    (hab : Filter.Eventually (fun z => ‖a z‖ ≤ Ca)
      (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure G).restrict k)))
    {g : P → G → ℂ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ∫ z in k, a z * g p z) := by
  exact continuousSetIntegralCompactGenMulV2 hk ha hab hg

end Work.BoseBoxFock
