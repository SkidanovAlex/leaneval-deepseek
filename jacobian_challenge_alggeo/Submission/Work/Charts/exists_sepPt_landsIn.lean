import Mathlib
import Submission.Work.Charts.FinBC
import Submission.Work.Charts.exists_fpt_of_opens_of_isSepClosed
import Submission.Work.Charts.finiteDimensional_resField_of_isClosed
import Submission.Work.Domain.Resid.exists_resPt_factor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Work.Charts

/-- **B3 (SEP-PT).** A nonempty open subscheme `U` of a `K`-scheme `X` dominated by a smooth,
geometrically irreducible `K`-scheme `Y` of finite type through a proper surjection `q : Y ⟶ X`
contains the image of a `k₁`-point of `X`, for some finite separable subextension
`k₁ ⊆ SeparableClosure K`.

The proof follows route B of the lead notes: write `Ks := SeparableClosure K`, base change `Y`
along `Spec Ks ⟶ Spec K` to `Y' : Sch Ks`, and use that a smooth, geometrically irreducible
scheme of finite type over the separably closed field `Ks` has a `Ks`-point in every nonempty
open (`exists_fpt_of_opens_of_isSepClosed`). Pushing this point through `Y' ⟶ Y ⟶ X` gives a
`Ks`-point `P` of `X` whose image point `e` is closed in `X`: `P.left` is a composite of a
closed immersion (the section `p` of `Y' ⟶ Spec Ks`), the integral (hence closed) projection
`Y' ⟶ Y` and the proper (hence closed) `q`. Zariski's lemma
(`finiteDimensional_resField_of_isClosed`) then makes `κ(e)` finite over `K`, and
`exists_resPt_factor` realises `e` as the image of a point over an intermediate field
`k₁ ⊆ Ks` of finite dimension. -/
theorem exists_sepPt_landsIn {K : Type u} [Field K] {X Y : Work.GCBasics.Sch K}
    [AlgebraicGeometry.IsIntegral X.left]
    [AlgebraicGeometry.Smooth Y.hom] [AlgebraicGeometry.GeometricallyIrreducible Y.hom]
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
    [AlgebraicGeometry.LocallyOfFiniteType X.hom] (q : Y ⟶ X)
    (hproper : AlgebraicGeometry.IsProper q.left) (hq : Function.Surjective q.left.base)
    (U : X.left.Opens) (hU : U ≠ ⊥) :
    ∃ (k₁ : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K ↥k₁),
      ∃ E : Work.GCBasics.FPt X ↥k₁, E.LandsIn U := by
  -- The separably closed base field and the base change `Y'` of `Y` along `Spec Ks ⟶ Spec K`.
  let Ks := SeparableClosure K
  let Y' : Work.GCBasics.Sch Ks :=
    Over.mk (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks))))
  let U' : Y'.left.Opens :=
    (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))) ⁻¹ᵁ (q.left ⁻¹ᵁ U)
  haveI : Smooth Y'.hom :=
    show Smooth (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))) from
      inferInstance
  haveI : GeometricallyIrreducible Y'.hom :=
    show GeometricallyIrreducible
        (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))) from inferInstance
  haveI : LocallyOfFiniteType Y'.hom := inferInstance
  -- `U'` is the preimage of `U` in `Y'`; it is nonempty because `q` and the base change are
  -- surjective and `U` is nonempty.
  have hU' : U' ≠ ⊥ := by
    have hUne : (U : Set X.left).Nonempty := by
      by_contra hne
      exact hU (SetLike.coe_injective
        (by rw [Set.not_nonempty_iff_eq_empty.mp hne, TopologicalSpace.Opens.coe_bot]))
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨y, hy⟩ := hq x
    haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K Ks)) :
        Spec (CommRingCat.of Ks) ⟶ Spec (CommRingCat.of K)) := inferInstance
    have hfst : Function.Surjective
        (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))).base :=
      Scheme.Hom.surjective _
    obtain ⟨z, hz⟩ := hfst y
    have hzmem : (q.left.base
        ((pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))).base z)) ∈ U := by
      rw [hz, hy]; exact hx
    have hz' : z ∈ U' := hzmem
    intro h
    rw [h] at hz'
    exact hz'
  -- A `Ks`-point of `Y'` in `U'`.
  obtain ⟨p, hp⟩ := Work.Charts.exists_fpt_of_opens_of_isSepClosed (K := Ks) Y' U' hU'
  -- `p` is a section of the projection `Y' ⟶ Spec Ks`.
  have hpcond : p.left ≫ pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))
      = 𝟙 (Spec (CommRingCat.of Ks)) := by
    have h := Over.w p
    rw [show Y'.hom = pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))
        from rfl] at h
    rw [show (Work.GCBasics.specOf Ks Ks).hom = 𝟙 (Spec (CommRingCat.of Ks)) from by
      rw [Work.GCBasics.specOf_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]]
      at h
    exact h
  -- Push `p` forward to a `Ks`-point `P` of `X`.
  have key : (p.left ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))
        ≫ q.left) ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ks)) := by
    rw [Category.assoc, Category.assoc]
    rw [Over.w q]
    rw [pullback.condition (f := Y.hom) (g := Spec.map (CommRingCat.ofHom (algebraMap K Ks)))]
    rw [← Category.assoc, hpcond]
    exact Category.id_comp _
  let P : Work.GCBasics.FPt X Ks :=
    Over.homMk (p.left ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))
      ≫ q.left) key
  have hPlands : Work.GCBasics.RPt.LandsIn P U := hp
  let e : X.left := P.left (IsLocalRing.closedPoint Ks)
  -- Closedness of the image point `e`.
  have hpci : IsClosedImmersion p.left :=
    isClosedImmersion_of_comp_eq_id Y'.hom p.left hpcond
  have hpmap : IsClosedMap ⇑p.left :=
    (IsClosedImmersion.isClosedEmbedding p.left).isClosedMap
  haveI : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)) :
      Spec (CommRingCat.of Ks) ⟶ Spec (CommRingCat.of K)) := by
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.IsIntegral.isIntegral
  haveI : IsIntegralHom (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))) :=
    inferInstance
  have hfstmap : IsClosedMap
      ⇑(pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))) :=
    Scheme.Hom.isClosedMap _
  haveI : UniversallyClosed q.left := inferInstance
  have hqmap : IsClosedMap ⇑q.left := Scheme.Hom.isClosedMap _
  have hPmap : IsClosedMap ⇑P.left := by
    have h1 : ⇑P.left = ⇑q.left
        ∘ ⇑(pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))) ∘ ⇑p.left := by
      funext x
      rfl
    rw [h1]
    have h2 : IsClosedMap
        (⇑(pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ks)))) ∘ ⇑p.left) :=
      IsClosedMap.comp hfstmap hpmap
    exact IsClosedMap.comp hqmap h2
  have heclosed : IsClosed ({e} : Set X.left) := by
    haveI : Subsingleton ↥(Over.left (Work.GCBasics.specOf K Ks)) :=
      ⟨fun a b => Subsingleton.elim (α := ↥(Spec (CommRingCat.of Ks))) a b⟩
    have hcl : IsClosed
        ({IsLocalRing.closedPoint Ks} : Set ↥(Over.left (Work.GCBasics.specOf K Ks))) := by
      have hs : ({IsLocalRing.closedPoint Ks} :
          Set ↥(Over.left (Work.GCBasics.specOf K Ks))) = Set.univ :=
        Set.eq_univ_of_forall (fun y => Subsingleton.elim y _)
      rw [hs]; exact isClosed_univ
    have h := hPmap ({IsLocalRing.closedPoint Ks} :
      Set ↥(Over.left (Work.GCBasics.specOf K Ks))) hcl
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_image]
    constructor
    · intro hy; exact ⟨IsLocalRing.closedPoint Ks, rfl, hy.symm⟩
    · rintro ⟨x, hx, hy⟩; rw [hx] at hy; exact hy.symm
  -- The residue field of `e` is finite over `K` (Nullstellensatz).
  have hfin : FiniteDimensional K (Work.GCBasics.resField X e) :=
    Work.Charts.finiteDimensional_resField_of_isClosed e heclosed
  -- Realise the point `e` over the finite-dimensional subfield `e'.fieldRange ⊆ Ks`.
  obtain ⟨e', _he'⟩ := Work.Domain.Resid.exists_resPt_factor (X := X) e (F := Ks) P (by rfl)
  have heU : e ∈ U := hPlands
  have hpE : (Work.GCBasics.RPt.map (e'.equivFieldRange).toAlgHom (Work.GCBasics.resPt X e)).left
      (IsLocalRing.closedPoint ↥e'.fieldRange) = e := by
    rw [Work.GCBasics.RPt.map, Over.comp_left]
    exact (Scheme.Hom.comp_apply _ _ _).trans (Work.GCBasics.resPt_apply X e _)
  refine ⟨e'.fieldRange, ?_, Work.GCBasics.RPt.map (e'.equivFieldRange).toAlgHom
    (Work.GCBasics.resPt X e), ?_⟩
  · exact FiniteDimensional.of_surjective (e'.equivFieldRange).toLinearMap
      (e'.equivFieldRange).surjective
  · show (Work.GCBasics.RPt.map (e'.equivFieldRange).toAlgHom (Work.GCBasics.resPt X e)).left
      (IsLocalRing.closedPoint ↥e'.fieldRange) ∈ U
    rw [hpE]
    exact heU

end Work.Charts
