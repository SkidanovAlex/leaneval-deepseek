import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Bridge
import Submission.Work.Orient.Boundary.RelativeFundamentalClassExistsOfCollar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# ORIENT: the orientation theory of a transverse preimage (item 3)

This file is the **orientation theory half** of the preimage theorem consumed by
`Submission/Work/ThomBordism/Transversality/README.md` (§4, the "no plan" item):

> the orientation of the ambient manifold together with the Thom class/orientation of the normal
> bundle orient the preimage and give a relative fundamental class which is a local generator at
> every interior point, with boundary the sum of the pieces' fundamental classes.

The **geometric half** (that a transverse preimage *is* a compact manifold with boundary, with the
boundary the end preimage, and that transversality produces the orientation family) is the input
`Work.ThomBordism.Transversality.TransversalPreimageTheorem`; what this file adds is that, *given* an
orientation family on the preimage (the exact output of that geometric input), the relative
fundamental class and its two properties exist — this is the content of item 2 of the ORIENT
deliverable (`Work.Orient.RelativeFundamentalClassExists`), applied at dimension `9` to the
cylinder/disk-with-holes of the Pontryagin–Thom construction.

Main result: `Work.Orient.exists_relFundClass_of_halfOrientation` — from
`Work.Orient.RelativeFundamentalClassExists 8`, every compact `C^∞` `9`-manifold with boundary
carrying an orientation family has a relative fundamental class `w ∈ H_9(W, ∂W; ℤ)` which

* is a local generator at every interior point **in the exact form of the field
  `Work.ThomBordism.NullBordismFamily.w_fund`** (`Work.ThomBordism.relChainsInclPunct`), and
* has boundary `hPairδ w` a fundamental class of `∂W` — i.e., with the convention of
  `Work.Orient.BoundaryOrientationConvention`, the class `[∂W]` of the induced boundary
  orientation; identifying `∂W` with the disjoint union of the pieces (the homeomorphism `e` of
  `Work.ThomBordism.Transversality.TransversalPullback`) turns this into the field `hw`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient

noncomputable section

/-- **The relative fundamental class of a transverse preimage**, from the existence theorem of item 2
and an orientation family on the preimage.  The three conclusions are, in order: the ORIENT property
`IsRelFundClass`; the same property in the exact form of the consumers' field
`Work.ThomBordism.NullBordismFamily.w_fund`; and the boundary formula (whose identification with the
sum of the pieces' classes is the Transversality chapter's data `e`). -/
theorem exists_relFundClass_of_halfOrientation (h : RelativeFundamentalClassExists 8)
    (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W] [CompactSpace W] [T2Space W]
    [Nonempty W]
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
      LocH (TopCat.of W) 9 x)
    (hγ : IsHalfOrientationFamily 8 (TopCat.of W) γ) :
    ∃ w : (Work.Cohomology.relChains (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9,
      IsRelFundClass (TopCat.of W) 9 ((modelWithCornersEuclideanHalfSpace 9).boundary W) w ∧
        (∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
          Submodule.span ℤ {((HomologicalComplex.homologyMap
            (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
              ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom w)} = ⊤) ∧
        IsFundClass (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8
          (Work.Cohomology.hPairδ (TopCat.of W)
            ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8 w) := by
  obtain ⟨w, hw1, hw2⟩ := h (TopCat.of W) γ hγ
  refine ⟨w, hw1, ?_, hw2⟩
  intro x hx
  rw [← relPunct_eq_relChainsInclPunct (TopCat.of W)
    ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx]
  exact hw1 x hx

/-- **The relative fundamental class of a transverse preimage, from the collar neighbourhood
theorem.**  This is `Work.Orient.exists_relFundClass_of_halfOrientation` with the existence theorem
of item 2 supplied by `Work.Orient.Boundary.RelativeFundamentalClassExists_of_hasCollar`: the only
remaining input is the collar neighbourhood theorem for compact `C^∞` `9`-manifolds with boundary,
which is the named input `Work.Surgery.HasCollar` of the Surgery area. -/
theorem exists_relFundClass_of_hasCollar
    (h : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ChartedSpace (EuclideanHalfSpace 9) M]
      [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M], Work.Surgery.HasCollar 8 M)
    (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W] [CompactSpace W] [T2Space W]
    [Nonempty W]
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W →
      LocH (TopCat.of W) 9 x)
    (hγ : IsHalfOrientationFamily 8 (TopCat.of W) γ) :
    ∃ w : (Work.Cohomology.relChains (TopCat.of W)
        ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9,
      IsRelFundClass (TopCat.of W) 9 ((modelWithCornersEuclideanHalfSpace 9).boundary W) w ∧
        (∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
          Submodule.span ℤ {((HomologicalComplex.homologyMap
            (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
              ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9).hom w)} = ⊤) ∧
        IsFundClass (TopCat.of ((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8
          (Work.Cohomology.hPairδ (TopCat.of W)
            ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8 w) :=
  exists_relFundClass_of_halfOrientation
    (Work.Orient.Boundary.RelativeFundamentalClassExists_of_hasCollar 8 h) W γ hγ

end

end Work.Orient
