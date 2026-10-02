import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.RelChainsBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local-generator family of a global relative class is a half-orientation family

`Work.ThomBordism.isHalfOrientationFamily_relChainsInclPunct`: if `w ∈ H₉(W, ∂W)` restricts, at every
interior point `x`, to a **generator** of the local group `H₉(W, W∖{x})`, then the resulting family

    γ x hx = (relChainsInclPunct W ∂W x hx)₉ w

is a **half-orientation family** in the sense of `Work.Orient.IsHalfOrientationFamily 8 W`.

The first clause of `IsHalfOrientationFamily` is exactly the hypothesis.  The second (the *coherence*
clause) is the standard fact that the local classes of one global relative class are compatible: for a
coordinate half-ball `K` inside the interior (`K ∩ ∂W = ∅`, so `∂W ⊆ Kᶜ`) the class

    a := (relChainsIncl W (∂W ⊆ Kᶜ))₉ w ∈ H₉(W, W∖K)

is the required class, and its restriction to `{x}`, `x ∈ K`, is `γ x hx` — a purely chain-level
functoriality (`Work.Orient.relChainsIncl_trans`) combined with the definition of
`relChainsInclPunct`.  The "coordinate half-ball" hypothesis on `K` is not used beyond the fact that
`K` is disjoint from the boundary (which is assumed).
-/

open CategoryTheory

namespace Work.ThomBordism

theorem isHalfOrientationFamily_relChainsInclPunct {W : TopCat}
    [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W]
    (w : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9)
    (hw : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W),
      Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct W
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9 w)} = ⊤) :
    Work.Orient.IsHalfOrientationFamily 8 W
      (fun x hx => HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct W
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9 w) := by
  classical
  refine ⟨fun x hx => hw x hx, ?_⟩
  intro K hK hKint
  -- `K` is disjoint from the boundary, so the boundary is contained in `Kᶜ`
  have hsub : (modelWithCornersEuclideanHalfSpace 9).boundary W ⊆ Kᶜ :=
    fun y hy hyK => hKint y hyK hy
  -- the class over the piece `K`: the image of `w` in `H₉(W, W∖K)`
  refine ⟨(HomologicalComplex.homologyMap (Work.Orient.relChainsIncl W hsub) 9).hom w, ?_⟩
  intro x hx hxK
  have hcomp : Kᶜ ⊆ ({x} : Set W)ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxK)
  -- functoriality: the composite `∂W ⊆ Kᶜ ⊆ {x}ᶜ` is the inclusion appearing in
  -- `relChainsInclPunct`
  have hkey : Work.Orient.relChainsIncl W hsub ≫ Work.Orient.relChainsIncl W hcomp
      = Work.ThomBordism.relChainsInclPunct W
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx := by
    rw [Work.Orient.relChainsIncl_trans]
    exact (Work.Orient.relChainsIncl_congr W (hsub.trans hcomp)
      (fun y hy hyx => hx (hyx ▸ hy))).trans rfl
  rw [Work.Orient.resRelH_eq_homologyMap_relChainsIncl]
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, hkey]
  rfl

end Work.ThomBordism
