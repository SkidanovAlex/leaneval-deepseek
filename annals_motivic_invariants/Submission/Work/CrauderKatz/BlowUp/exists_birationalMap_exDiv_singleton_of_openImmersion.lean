import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.trans_toRationalMap
import Submission.Work.Motivic.trans_hom_apply

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.CrauderKatz.BlowUp

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Order

noncomputable section

/-! ## Auxiliary facts about partial maps

The main theorem below is about the behaviour of the inverse of a dominant open immersion at a
codimension-one point of the target that is *not* in the image.  The mathematical content is
that such a point is not an isomorphism point of the inverse rational map: a partial
isomorphism realising the inverse would have to be defined at that point, and comparing it
with the open immersion on a dense open forces it to agree with the inverse everywhere it is
defined --- in particular the missing point would lie in the image.

We first record the elementary lemma that a partial map from a reduced and separated scheme to
itself whose rational map is the identity is the inclusion of its domain. -/

/-- For the identity partial map of `Y`, restricting to a smaller open and then forgetting the
restriction gives the inclusion of that open. -/
lemma id_restrict_hom (Y : Scheme.{0}) (W : Y.Opens) (hW : Dense (W : Set Y))
    (hWr : W ≤ (PartialMap.id Y).domain) :
    ((PartialMap.id Y).restrict W hW hWr).hom = W.ι := by
  rw [PartialMap.restrict_hom, PartialMap.id_hom]
  rw [show Y.topIso.hom = (⊤ : Y.Opens).ι from rfl]
  exact Scheme.homOfLE_ι Y hWr

/-- A partial isomorphism realises its own rational map, hence every point of its source is an
isomorphism point of the associated birational map. -/
lemma isIsoAt_of_mem_source {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (i : X.PartialIso Y) {x : X} (hx : x ∈ i.source) : IsIsoAt i.toBirationalMap x :=
  ⟨i, hx, rfl⟩

/-- **A partial map from a reduced and separated scheme to itself whose rational map is the
identity is the inclusion of its domain.**  Equivalently: two partial maps from a reduced
scheme to a separated scheme which represent the same rational map agree at every common point
of their domains.

This is the point-level content of `PartialMap.equiv_iff_of_isSeparated`, stated without a base
scheme: the separating morphism can be taken to be the map to the terminal object, which is
separated exactly because `Y` is. -/
theorem value_eq_self {Y : Scheme.{0}} [IrreducibleSpace Y] [IsReduced Y] [Y.IsSeparated]
    (f : Y.PartialMap Y) (hf : f.toRationalMap = RationalMap.id Y) {y : Y}
    (hy : y ∈ f.domain) : f.hom ⟨y, hy⟩ = y := by
  obtain ⟨W, hW, hWl, hWr, heq⟩ := PartialMap.toRationalMap_eq_iff.mp hf
  haveI hd : IsDominant (Y.homOfLE hWl) := Opens.isDominant_homOfLE hW hWl
  have hR : ((PartialMap.id Y).restrict W hW hWr).hom = W.ι := id_restrict_hom Y W hW hWr
  have hL : Y.homOfLE hWl ≫ f.hom = W.ι := by
    have heq' : Y.homOfLE hWl ≫ f.hom = ((PartialMap.id Y).restrict W hW hWr).hom := heq
    rw [heq', hR]
  have hmain : f.hom = f.domain.ι := by
    refine ext_of_isDominant (Y.homOfLE hWl) ?_
    rw [hL]
    rw [Scheme.homOfLE_ι]
  rw [hmain]
  exact (Scheme.Opens.ι_apply _ _).trans rfl

/-- **The inverse of a dominant open immersion is not an isomorphism at a point of the target
outside the image.**  If `i : Y.PartialIso X` represents the rational map inverse to a partial
isomorphism `A : X.PartialIso Y` which is defined everywhere (`A.source = ⊤`), then the source
of `i` is contained in the target of `A`: the composite `i.trans A` is a partial isomorphism of
`Y` whose rational map is the identity, so by `value_eq_self` its values are the points
themselves, while by `Work.Motivic.trans_hom_apply` its values lie in the image of `A`. -/
theorem mem_target_of_toRationalMap_eq_symm {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsReduced Y] [Y.IsSeparated] (i : Y.PartialIso X) (A : X.PartialIso Y)
    (hA : A.source = ⊤) (h : i.toRationalMap = A.symm.toRationalMap) {y : Y}
    (hy : y ∈ i.source) : y ∈ A.target := by
  let w : X := i.toPartialMap.hom ⟨y, hy⟩
  have hAtriv : w ∈ A.source := by rw [hA]; trivial
  -- the rational map of the composite partial map `X ⤏ X` on the `Y`-side is the identity
  have hgrat : (i.toPartialMap.comp A.toPartialMap).toRationalMap = RationalMap.id Y := by
    refine PartialMap.toRationalMap_eq_iff.mpr ?_
    have h1 : i.toPartialMap.equiv A.symm.toPartialMap := PartialMap.toRationalMap_eq_iff.mp h
    refine (PartialMap.comp_equiv_of_equiv_left h1 A.toPartialMap).trans ?_
    rw [PartialIso.symm_toPartialMap_comp]
    exact PartialMap.restrict_equiv (PartialMap.id Y) A.target A.dense_target le_top
  have hkrat : (i.trans A).toRationalMap = RationalMap.id Y := by
    rw [Work.Motivic.trans_toRationalMap, RationalMap.toRationalMap_comp]
    exact hgrat
  have hksrc : y ∈ (i.trans A).source := (Work.Motivic.mem_trans_source i A hy).mpr hAtriv
  have hv : (i.trans A).toPartialMap.hom ⟨y, hksrc⟩ = y :=
    value_eq_self (i.trans A).toPartialMap hkrat hksrc
  have hmem : (i.trans A).toPartialMap.hom ⟨y, hksrc⟩ ∈ (A.target : Set Y) := by
    rw [Work.Motivic.trans_hom_apply i A hy hAtriv, PartialIso.toPartialMap_hom]
    change A.target.ι (A.iso.hom ⟨w, hAtriv⟩) ∈ (A.target : Set Y)
    exact (A.iso.hom ⟨w, hAtriv⟩).2
  rw [← hv]
  exact hmem

/-! ## The partial isomorphism of an open immersion -/

/-- The partial isomorphism attached to a dominant open immersion `ι : X ⟶ Y`: it is the
identification of `X` with its image, with source all of `X` and target `ι.opensRange`. -/
noncomputable def opensRangePartialIso {X Y : Scheme.{0}} (ι : X ⟶ Y) [IsOpenImmersion ι]
    [IsDominant ι] : X.PartialIso Y where
  source := ⊤
  dense_source := dense_univ
  target := ι.opensRange
  dense_target := ι.denseRange
  iso := X.topIso ≪≫ ι.isoOpensRange

@[simp]
lemma opensRangePartialIso_source {X Y : Scheme.{0}} (ι : X ⟶ Y) [IsOpenImmersion ι]
    [IsDominant ι] : (opensRangePartialIso ι).source = ⊤ := rfl

@[simp]
lemma opensRangePartialIso_target {X Y : Scheme.{0}} (ι : X ⟶ Y) [IsOpenImmersion ι]
    [IsDominant ι] : (opensRangePartialIso ι).target = ι.opensRange := rfl

/-! ## The main theorem -/

/-- A dominant open immersion that misses exactly one point of codimension one yields a birational map whose forward exceptional divisor is that point and whose inverse exceptional divisor is empty. The forward map is the inverse of the immersion, defined on the image; the missing point is the only codimension-one point of the target outside the image. -/
theorem exists_birationalMap_exDiv_singleton_of_openImmersion (𝕜 : Type) [Field 𝕜]
    {X Y : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [AlgebraicGeometry.IsReduced Y]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [AlgebraicGeometry.IsSeparated (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (ι : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion ι] (hdense : DenseRange ι)
    (y : Y) (hy : Order.coheight y = 1) (hyr : y ∉ Set.range ι)
    (huniq : ∀ y' : Y, Order.coheight y' = 1 → y' ∉ Set.range ι → y' = y) :
    ∃ φ : Y.BirationalMap X, exDiv φ = {y} ∧ exDiv φ.symm = ∅ := by
  haveI hdom : IsDominant ι := ⟨hdense⟩
  -- `Y` is separated as a scheme, since it is separated over `Spec 𝕜`
  haveI hYsep : Y.IsSeparated := by
    refine ⟨?_⟩
    rw [← Limits.terminal.comp_from (Y ↘ Spec (CommRingCat.of 𝕜))]
    infer_instance
  let A : X.PartialIso Y := opensRangePartialIso ι
  have hAsrc : A.source = ⊤ := rfl
  have hAtgt : A.target = ι.opensRange := rfl
  -- every point in the image is an isomorphism point of the inverse
  have hisoAt_of_mem : ∀ z ∈ Set.range ι, IsIsoAt A.symm.toBirationalMap z := by
    rintro z ⟨x, rfl⟩
    refine ⟨A.symm, ?_, rfl⟩
    rw [PartialIso.symm_source, hAtgt]
    exact (Hom.mem_opensRange).mpr ⟨x, rfl⟩
  -- and the missing point is not
  have hnotIsoAt : ¬ IsIsoAt A.symm.toBirationalMap y := by
    rintro ⟨i, hyi, hr⟩
    have hmem : y ∈ A.target :=
      mem_target_of_toRationalMap_eq_symm i A hAsrc (by rw [hr, PartialIso.toBirationalMap_hom]) hyi
    exact hyr ((Hom.mem_opensRange).mp (by rw [← hAtgt]; exact hmem))
  refine ⟨A.symm.toBirationalMap, ?_, ?_⟩
  · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hy, hnotIsoAt⟩, ?_⟩
    rintro z ⟨hz1, hz2⟩
    by_contra hzy
    refine hz2 (hisoAt_of_mem z ?_)
    by_contra hzr
    exact hzy (huniq z hz1 hzr)
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hz⟩
    -- the inverse of the inverse is the original partial isomorphism
    have hsymm : (A.symm.toBirationalMap).symm = A.toBirationalMap := by
      apply BirationalMap.ext
      rw [BirationalMap.symm_hom, PartialIso.toBirationalMap_inv,
        show A.symm.symm = A from rfl, PartialIso.toBirationalMap_hom]
    rw [hsymm] at hz
    exact hz (isIsoAt_of_mem_source A (by rw [hAsrc]; trivial))

end

end Work.CrauderKatz.BlowUp
