import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

theorem ncard_PairSet_le (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (U : Finset K) (a : mixedEmbedding.mixedSpace K)
    (hfin : (Xset K I R a).Finite) :
    (PairSet K I R U a).ncard ≤ (Xset K I R a).ncard * (Xset K I R a).ncard := by
  have hsub : PairSet K I R U a ⊆ (Xset K I R a) ×ˢ (Xset K I R a) := by
    rintro p ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  calc (PairSet K I R U a).ncard
      ≤ ((Xset K I R a) ×ˢ (Xset K I R a)).ncard :=
        Set.ncard_le_ncard hsub (hfin.prod hfin)
    _ = (Xset K I R a).ncard * (Xset K I R a).ncard := Set.ncard_prod

end Work.Geometry
