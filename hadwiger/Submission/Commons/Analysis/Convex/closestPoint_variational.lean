import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Commons.Analysis.Convex

lemma closestPoint_variational
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] {D : Set V} (hD : Convex ℝ D) {q p : V}
    (hpD : p ∈ D) (hmin : ∀ y ∈ D, ‖q - p‖ ≤ ‖q - y‖) :
    ∀ z ∈ D, inner ℝ (q - p) (z - p) ≤ 0 := by
  intro z hz
  let _ : Nonempty D := ⟨⟨p, hpD⟩⟩
  -- Show that ‖q - p‖ is the infimum of distances from q to points of D.
  have hinf : ‖q - p‖ = ⨅ w : D, ‖q - (w : V)‖ := by
    apply le_antisymm
    · refine le_ciInf ?_
      intro w
      exact hmin (w : V) w.2
    · have hb : BddBelow (Set.range fun w : D => ‖q - (w : V)‖) :=
        ⟨0, by rintro y ⟨w, rfl⟩; exact norm_nonneg _⟩
      simpa using (ciInf_le hb ⟨p, hpD⟩ : ⨅ w : D, ‖q - (w : V)‖ ≤ ‖q - p‖)
  exact (norm_eq_iInf_iff_real_inner_le_zero hD hpD).mp hinf z hz

end Commons.Analysis.Convex