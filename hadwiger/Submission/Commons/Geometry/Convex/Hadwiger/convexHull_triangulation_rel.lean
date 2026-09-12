import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.convexHull_triangulation_rel_main

open scoped BigOperators

namespace Commons.Geometry.Convex.Hadwiger

theorem convexHull_triangulation_rel {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Finset V) (hS : S.Nonempty) :
    let d : ℕ := Module.finrank ℝ (affineSpan ℝ (S : Set V)).direction
    ∃ (ι : Type) (_ : Fintype ι), ∃ A : ι → Set V,
      ∃ w : ι → Fin (d + 1) → V,
        (⋃ i : ι, A i = convexHull ℝ (S : Set V)) ∧
        (∀ i : ι, A i = convexHull ℝ (Set.range (w i))) ∧
        (∀ i : ι, AffineIndependent ℝ (w i)) ∧
        (∀ i j : ι, i ≠ j →
          Disjoint (intrinsicInterior ℝ (A i)) (intrinsicInterior ℝ (A j))) := by
  exact convexHull_triangulation_rel_main S hS

end Commons.Geometry.Convex.Hadwiger
