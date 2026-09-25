import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

/-- The set `Xset K I R a` of lattice points of the coset `a + Λ` in the window `B_R` is
finite: it is the translate by `a` of the intersection of the `ℤ`-lattice `Lattice K I` with
a bounded set, and such an intersection is finite by `ZSpan.setFinite_inter`. -/
theorem finite_Xset (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (a : mixedEmbedding.mixedSpace K) :
    (Xset K I R a).Finite := by
  rw [Xset_eq_vadd, Set.finite_vadd_set, Set.inter_comm]
  refine ZSpan.setFinite_inter (mixedEmbedding.fractionalIdealLatticeBasis K I) ?_
  have hball : {y : mixedEmbedding.mixedSpace K | a + y ∈ Window K R} = Metric.ball (-a) R := by
    ext y
    rw [Window_eq_ball]
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    rw [dist_eq_norm, sub_neg_eq_add, add_comm y]
  rw [hball]
  exact Metric.isBounded_ball

end Work.Geometry
