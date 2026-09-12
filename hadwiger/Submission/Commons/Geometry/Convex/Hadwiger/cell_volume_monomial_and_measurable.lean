import Mathlib
import Submission.Commons.Geometry.Convex.cell_volume_monomial_and_measurable

open scoped Classical

namespace Commons.Geometry.Convex.Hadwiger

theorem cell_volume_monomial_and_measurable
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (P F : Set V) (hFP : F ⊆ P) (hFne : F.Nonempty) (hFcl : IsClosed F)
    (hFcvx : Convex ℝ F) (hFbd : Bornology.IsBounded F)
    (t : ℝ) (ht : 0 ≤ t) :
    let NC : Set V := {z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y}
    let cell : ℝ → Set V := fun s : ℝ =>
      Set.image2 (fun (x y : V) => x + y) (intrinsicInterior ℝ F) (NC ∩ Metric.closedBall (0 : V) s)
    MeasurableSet (cell t) ∧
    MeasureTheory.volume (cell t) =
      ENNReal.ofReal (t ^ Module.finrank ℝ (Submodule.orthogonal (affineSpan ℝ F).direction)) *
        MeasureTheory.volume (cell 1) := by
  exact Commons.Geometry.Convex.cell_volume_monomial_and_measurable P F hFP hFne hFcl hFcvx hFbd t ht

end Commons.Geometry.Convex.Hadwiger
