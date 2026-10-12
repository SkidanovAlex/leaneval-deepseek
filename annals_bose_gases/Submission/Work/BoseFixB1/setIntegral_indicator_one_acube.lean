import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxOpA
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem setIntegral_indicator_one_acube {a : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ y in Submission.BoseGases.acube a,
        (A.indicator (fun _ => (1 : ℝ)) y) * g y)
      = ∫ y in A, g y := by
  -- Pointwise everywhere: `1_A * g = A.indicator g`.
  have hEq : (fun y : EuclideanSpace ℝ (Fin 3) =>
      A.indicator (fun _ => (1 : ℝ)) y * g y) = A.indicator g := by
    funext y
    by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  rw [hEq, MeasureTheory.setIntegral_indicator hAm, Set.inter_eq_right.mpr hAc]

end Work.BoseFixB1
