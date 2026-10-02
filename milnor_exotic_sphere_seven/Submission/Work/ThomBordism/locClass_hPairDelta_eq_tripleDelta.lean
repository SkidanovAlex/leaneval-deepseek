import Mathlib
import Submission.Work.Orient.Boundary.BoundaryOrientation
import Submission.Work.Orient.Boundary.TripleSetup
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- The local class at a boundary point `y` of the connecting map `hPairδ W ∂W n w` of the pair
`(W, ∂W)` is the image, under the comparison `diffCokerMap` of the two models of the local group,
of the connecting map of the **triple** `∂W∖{y} ⊆ ∂W ⊆ W` applied to `w`.

This is the "algebraic" half of `Work.Orient.Boundary.BoundaryOrientation` (Hatcher 3.43): it
identifies the local class of the boundary class with the localisation of the connecting map of the
triple.  The geometric input (that this class generates) is *not* used here, so the statement holds
for an arbitrary `w`. -/
theorem locClass_hPairDelta_eq_tripleDelta (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (w : (Work.Cohomology.relChains W (Work.Orient.Boundary.bdrySetW n W)).homology (n + 1))
    (y : W) (hy : y ∈ Work.Orient.Boundary.bdrySetW n W) :
    Work.Orient.locClass (TopCat.of ↥(Work.Orient.Boundary.bdrySetW n W)) n
        (Work.Cohomology.hPairδ W (Work.Orient.Boundary.bdrySetW n W) n w) ⟨y, hy⟩
      = (HomologicalComplex.homologyMap (Work.Orient.Boundary.diffCokerMap W
          (Work.Orient.Boundary.bdrySetW n W) y hy
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)) n).hom
        ((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
          (Work.Orient.Boundary.bdrySetW n W) (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ
            (n + 1) n (by simp [ComplexShape.down]) w) := by
  -- Step 1: the projection of `hPairδ W ∂W n w` to the local group computed from `C_*(∂W∖{y})`
  -- is the connecting map of the triple `∂W∖{y} ⊆ ∂W ⊆ W`
  -- (`hPairδ_comp_localization_eq_tripleδ`).
  have h1 : (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChainsSub W (Work.Orient.Boundary.bdryMinus n W y)
          (Work.Orient.Boundary.bdrySetW n W)
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y))) n).hom
        (Work.Cohomology.hPairδ W (Work.Orient.Boundary.bdrySetW n W) n w)
      = ((Work.Cohomology.relChains_triple_shortExact W (Work.Orient.Boundary.bdryMinus n W y)
          (Work.Orient.Boundary.bdrySetW n W)
          (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)).δ (n + 1) n
          (by simp [ComplexShape.down])).hom w := by
    rw [← ModuleCat.comp_apply,
      Work.Orient.Boundary.hPairδ_comp_localization_eq_tripleδ n W y
        (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y)]
    rfl
  -- Step 2: the two models of the local group of `∂W` at `y` are compared by `diffCokerMap`
  -- (`diffCokerMap_localClass`).
  have h2 := Work.Orient.Boundary.diffCokerMap_localClass W
    (Work.Orient.Boundary.bdrySetW n W) y hy
    (Work.Orient.Boundary.bdryMinus_sub_bdrySetW n W y) n
    (Work.Cohomology.hPairδ W (Work.Orient.Boundary.bdrySetW n W) n w)
  rw [h1] at h2
  -- `locClass` is, definitionally, the localisation through `C_*(↥∂W ∖ {y})`.
  rw [h2]
  rfl

end Work.ThomBordism
