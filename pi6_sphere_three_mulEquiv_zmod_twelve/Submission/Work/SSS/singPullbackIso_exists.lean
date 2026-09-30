import Mathlib
import Submission.Work.SSS.piszDefs
import Submission.Work.StemsB.Fibrations

/-!
# The singular simplicial set of a topological pullback

For continuous maps `p : E → B` and `q : E' → B`, the topological pullback (fibre product)
`Work.StemsB.Pullback p q = {x : E × E' // p x.1 = q x.2}` has, as its singular simplicial set,
the pullback of the singular simplicial sets of `E` and `E'` over that of `B`:

  `Sing (E ×_B E') ≅ Sing E ×_{Sing B} Sing E'`,

naturally in the projections.  This is the elementary ingredient behind the fact that the Serre
spectral sequence of a fibration is built from the fibres: the `E₁`-page of the spectral sequence
of `p` is computed from the singular chain complexes of the fibres, and base change of a fibration
along `q : E' → B` pulls the `σ`-pieces back along the projection `E ×_B E' → E`.

Mathematically this is the statement that the singular simplicial set functor
`TopCat.toSSet : TopCat ⥤ SSet` is a right adjoint (its left adjoint is geometric realization,
`sSetTopAdj`), hence preserves limits.  Formally, we use the explicit limit cone
`TopCat.pullbackConeIsLimit` for the pullback in `TopCat`, transport it to `SSet` along
`isLimitOfPreserves`, and then change the shape of the diagram from `cospan f g ⋙ toSSet`
(where `f`, `g` are the maps in `TopCat`) to the equivalent `cospan (toSSet.map f) (toSSet.map g)`
using `diagramIsoCospan` and `PullbackCone.isoMk`.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The singular simplicial set of a topological pullback is the pullback of the singular
simplicial sets.**  For `p : E → B` and `q : E' → B` there is an isomorphism
`Sing (Pullback p q) ≅ pullback (Sing p) (Sing q)` carrying the two projections of the pullback to
the two projections of `p` and `q`. -/
theorem singPullbackIso_exists {E B E' : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace E'] (p : ContinuousMap E B) (q : ContinuousMap E' B) :
    ∃ e : CategoryTheory.Iso (Work.SSS.sSing (Work.StemsB.Pullback p q))
        (CategoryTheory.Limits.pullback (Work.SSS.sSingP p) (Work.SSS.sSingP q)),
      (CategoryTheory.CategoryStruct.comp e.hom
          (CategoryTheory.Limits.pullback.fst (Work.SSS.sSingP p) (Work.SSS.sSingP q))
        = Work.SSS.sSingP (Work.StemsB.pullbackFst p q)) ∧
      (CategoryTheory.CategoryStruct.comp e.hom
          (CategoryTheory.Limits.pullback.snd (Work.SSS.sSingP p) (Work.SSS.sSingP q))
        = Work.SSS.sSingP (Work.StemsB.pullbackSnd p q)) := by
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
  have hpbf : TopCat.toSSet.map (TopCat.pullbackFst f g) = sSingP (Work.StemsB.pullbackFst p q) := by
    rw [show TopCat.pullbackFst f g = TopCat.ofHom (Work.StemsB.pullbackFst p q) from by
      ext x; rfl]
    rfl
  have hpbs : TopCat.toSSet.map (TopCat.pullbackSnd f g) = sSingP (Work.StemsB.pullbackSnd p q) := by
    rw [show TopCat.pullbackSnd f g = TopCat.ofHom (Work.StemsB.pullbackSnd p q) from by
      ext x; rfl]
    rfl
  have hfst : c'.fst = sSingP (Work.StemsB.pullbackFst p q) := by
    rw [← hpbf]; rfl
  have hsnd : c'.snd = sSingP (Work.StemsB.pullbackSnd p q) := by
    rw [← hpbs]; rfl
  refine ⟨hc'.conePointUniqueUpToIso (pullback.isLimit (sSingP p) (sSingP q)), ?_, ?_⟩
  · exact (IsLimit.conePointUniqueUpToIso_hom_comp hc'
      (pullback.isLimit (sSingP p) (sSingP q)) WalkingCospan.left).trans hfst
  · exact (IsLimit.conePointUniqueUpToIso_hom_comp hc'
      (pullback.isLimit (sSingP p) (sSingP q)) WalkingCospan.right).trans hsnd

end

end Work.SSS
