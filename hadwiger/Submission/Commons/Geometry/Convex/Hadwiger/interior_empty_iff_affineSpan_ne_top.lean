import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

namespace Commons.Geometry.Convex.Hadwiger

/-- A convex body in a finite-dimensional real normed space has empty interior if and only if
it is not full-dimensional (its affine span is not the whole ambient space). -/
theorem interior_empty_iff_affineSpan_ne_top
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : ConvexBody V) :
    interior (K : Set V) = ∅ ↔ affineSpan ℝ (K : Set V) ≠ ⊤ := by
  constructor
  · intro h_empty
    intro htop
    have hne : (interior (K : Set V)).Nonempty :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top K.convex).mpr htop
    rw [h_empty] at hne
    exact (Set.not_nonempty_iff_eq_empty.mpr rfl) hne
  · intro h_ne_top
    by_contra h_not_empty
    have hne : (interior (K : Set V)).Nonempty := Set.nonempty_iff_ne_empty.mpr h_not_empty
    have htop : affineSpan ℝ (K : Set V) = ⊤ :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top K.convex).mp hne
    exact h_ne_top htop

end Commons.Geometry.Convex.Hadwiger