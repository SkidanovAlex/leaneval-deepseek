import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of the intrinsic interior

The intrinsic interior `intrinsicInterior ℝ s` of an arbitrary set `s` in a
finite-dimensional real normed space is measurable (for the Borel σ-algebra).

The key fact is topological: the intrinsic interior of `s` is the interior of
`s ∩ A` considered inside its affine span `A := affineSpan ℝ s` and then viewed
as a subset of the ambient space.  Inside `A` (which carries the subspace
topology) that interior is open, hence it is `A ∩ G` for some open set `G` of
the ambient space.  Since `A` is closed in the finite-dimensional space `V`,
`A ∩ G` is measurable.
-/

namespace Commons.Geometry.Convex

open Set Topology

/-- The affine span of any subset of a finite-dimensional real normed space is closed. -/
lemma isClosed_affineSpan_of_finiteDimensional
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) : IsClosed (affineSpan ℝ s : Set V) := by
  have hdir_closed : IsClosed ((affineSpan ℝ s).direction : Set V) := by
    exact Submodule.closed_of_finiteDimensional (𝕜 := ℝ) (affineSpan ℝ s).direction
  exact (AffineSubspace.isClosed_direction_iff (R := ℝ) (V := V) (P := V)
    (affineSpan ℝ s)).mp hdir_closed

/-- The intrinsic interior of any subset of a finite-dimensional real normed space is
a Borel measurable set. -/
theorem intrinsicInterior_measurableSet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (s : Set V) :
    MeasurableSet (intrinsicInterior ℝ s : Set V) := by
  rw [intrinsicInterior]
  -- The interior of the preimage is open in the affine span (a closed subspace of V),
  -- so it is the preimage of some ambient open set G.
  have hU : IsOpen (interior ((Subtype.val : affineSpan ℝ s → V) ⁻¹' s)) := isOpen_interior
  obtain ⟨G, hG, hGU⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hU
  -- The image of that interior under the closed embedding is `affineSpan ℝ s ∩ G`.
  have himage :
      (Subtype.val : affineSpan ℝ s → V) '' interior ((Subtype.val : affineSpan ℝ s → V) ⁻¹' s)
        = (affineSpan ℝ s : Set V) ∩ G := by
    rw [← hGU]
    ext x
    constructor
    · rintro ⟨y, hyG, rfl⟩
      exact ⟨Subtype.coe_prop y, hyG⟩
    · rintro ⟨hx, hxG⟩
      refine ⟨⟨x, hx⟩, hxG, rfl⟩
  rw [himage]
  exact (isClosed_affineSpan_of_finiteDimensional s).measurableSet.inter hG.measurableSet

end Commons.Geometry.Convex