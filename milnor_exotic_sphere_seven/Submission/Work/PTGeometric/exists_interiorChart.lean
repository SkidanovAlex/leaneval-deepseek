import Mathlib
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# An interior chart in the boundaryless model space

For a manifold `W` with boundary modelled on the half-space `EuclideanHalfSpace (n+1)`, and for any
point `z`, the extended chart `extChartAt I z` (where `I = modelWithCornersEuclideanHalfSpace (n+1)`)
can be shrunk so that its target is the **interior** of the original target (a subset of the
boundaryless model space `EuclideanSpace ℝ (Fin (n+1))`), while keeping the same underlying function
and inverse function.  The only points dropped from the source are boundary points of `W`, so the
source still contains every interior point of the source of `extChartAt I z`.
-/

set_option autoImplicit false

open scoped Manifold Topology
open Classical

namespace Work.PTGeometric

noncomputable section

/-- The extended chart at `z`, restricted to the preimage of the interior of its target.  Its target
is the interior of the target of the extended chart, so it is a chart into the boundaryless model
space on the interior points of `W`. -/
theorem exists_interiorChart (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (z : W) :
    ∃ e : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin (n + 1))),
      (⇑e = extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z) ∧
      (⇑e.symm = ⇑(extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).symm) ∧
      e.target = interior (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).target ∧
      (∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
        x ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) z).source → x ∈ e.source) := by
  set I := modelWithCornersEuclideanHalfSpace (n + 1) with hI
  set c := extChartAt I z with hc
  have hne : (1 : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨{ toFun := ⇑c
            invFun := ⇑c.symm
            source := c.source ∩ c ⁻¹' interior c.target
            target := interior c.target
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            continuousOn_toFun := ?_
            continuousOn_invFun := ?_
            open_source := ?_
            open_target := ?_ }, rfl, rfl, rfl, ?_⟩
  · intro y hy; exact hy.2
  · intro y hy
    refine ⟨c.map_target (interior_subset hy), ?_⟩
    rw [Set.mem_preimage, PartialEquiv.right_inv c (interior_subset hy)]
    exact hy
  · intro y hy; exact c.left_inv hy.1
  · intro y hy; exact c.right_inv (interior_subset hy)
  · exact (continuousOn_extChartAt (I := I) z).mono Set.inter_subset_left
  · exact (continuousOn_extChartAt_symm (I := I) z).mono interior_subset
  · exact isOpen_extChartAt_preimage' (I := I) z isOpen_interior
  · exact isOpen_interior
  · intro x hx hxs
    have hsrc : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source := by
      rw [← extChartAt_source (I := I) (x := z)]; exact hxs
    have hint : I.IsInteriorPoint x :=
      (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint (I := I) x).mpr hx
    have hval : extChartAt I z x ∈ interior (extChartAt I z).target :=
      (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := I) (M := W) hne
        (chart_mem_atlas (EuclideanHalfSpace (n + 1)) z) hsrc).mp hint
    exact ⟨hxs, hval⟩

end

end Work.PTGeometric
