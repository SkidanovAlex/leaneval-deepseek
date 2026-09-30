import Mathlib
import Submission.Work.SSSR.piszDefs
import Submission.Work.SSSR.StemsB.Fibrations
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
noncomputable section

/-- **The singular simplicial set of a topological pullback is the pullback of the singular
simplicial sets.**  For `p : E → B` and `q : E' → B` there is an isomorphism
`Sing (Pullback p q) ≅ pullback (Sing p) (Sing q)` carrying the two projections of the pullback to
the two projections of `p` and `q`. -/
theorem singPullbackIso_exists {E B E' : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace E'] (p : ContinuousMap E B) (q : ContinuousMap E' B) :
    ∃ e : CategoryTheory.Iso (Work.SSSR.sSing (Work.SSSR.StemsB.Pullback p q))
        (CategoryTheory.Limits.pullback (Work.SSSR.sSingP p) (Work.SSSR.sSingP q)),
      (CategoryTheory.CategoryStruct.comp e.hom
          (CategoryTheory.Limits.pullback.fst (Work.SSSR.sSingP p) (Work.SSSR.sSingP q))
        = Work.SSSR.sSingP (Work.SSSR.StemsB.pullbackFst p q)) ∧
      (CategoryTheory.CategoryStruct.comp e.hom
          (CategoryTheory.Limits.pullback.snd (Work.SSSR.sSingP p) (Work.SSSR.sSingP q))
        = Work.SSSR.sSingP (Work.SSSR.StemsB.pullbackSnd p q)) := by
  -- the two maps in `TopCat`
  let f := TopCat.ofHom p
  let g := TopCat.ofHom q
  -- the explicit limit cone of the pullback of `f` and `g` in `TopCat`
  have hlim : IsLimit (TopCat.pullbackCone f g) := TopCat.pullbackConeIsLimit f g
  -- its image under the right adjoint `TopCat.toSSet` is a limit cone
  let t : Cone (cospan f g ⋙ TopCat.toSSet) :=
    TopCat.toSSet.mapCone (TopCat.pullbackCone f g)
  have ht : IsLimit t := isLimitOfPreserves TopCat.toSSet hlim
  -- rewritten as a cone over the cospan `Sing p`, `Sing q` of simplicial sets
  let c' : PullbackCone (sSingP p) (sSingP q) :=
    PullbackCone.mk (t.π.app WalkingCospan.left) (t.π.app WalkingCospan.right)
      ((t.π.naturality WalkingCospan.Hom.inl).symm.trans (t.π.naturality WalkingCospan.Hom.inr))
  have hc' : IsLimit c' :=
    (IsLimit.equivOfNatIsoOfIso (diagramIsoCospan (cospan f g ⋙ TopCat.toSSet)) t c'
      (PullbackCone.isoMk t)) ht
  -- identification of the projections of the `TopCat` pullback with those of `Pullback p q`
  have hpbf : TopCat.toSSet.map (TopCat.pullbackFst f g) = sSingP (Work.SSSR.StemsB.pullbackFst p q) := by
    rw [show TopCat.pullbackFst f g = TopCat.ofHom (Work.SSSR.StemsB.pullbackFst p q) from by
      ext x; rfl]
    rfl
  have hpbs : TopCat.toSSet.map (TopCat.pullbackSnd f g) = sSingP (Work.SSSR.StemsB.pullbackSnd p q) := by
    rw [show TopCat.pullbackSnd f g = TopCat.ofHom (Work.SSSR.StemsB.pullbackSnd p q) from by
      ext x; rfl]
    rfl
  have hfst : c'.fst = sSingP (Work.SSSR.StemsB.pullbackFst p q) := by
    rw [← hpbf]; rfl
  have hsnd : c'.snd = sSingP (Work.SSSR.StemsB.pullbackSnd p q) := by
    rw [← hpbs]; rfl
  refine ⟨hc'.conePointUniqueUpToIso (pullback.isLimit (sSingP p) (sSingP q)), ?_, ?_⟩
  · exact (IsLimit.conePointUniqueUpToIso_hom_comp hc'
      (pullback.isLimit (sSingP p) (sSingP q)) WalkingCospan.left).trans hfst
  · exact (IsLimit.conePointUniqueUpToIso_hom_comp hc'
      (pullback.isLimit (sSingP p) (sSingP q)) WalkingCospan.right).trans hsnd

end

end Work.SSSR
