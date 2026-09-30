/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area DescentGeom (geometric half of area DS)
-/
import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Descent of separatedness along a base change of a field

`isSeparated_of_bc` is the descent statement used for the geometric properties of the descended
Jacobian `J`: if the base change `A_{k'}` of a `k`-scheme `A` is separated over `k'`, then `A` is
separated over `k`.

## The mathematical argument

Separatedness is *fpqc local on the base* (Stacks 02L6).  Rather than formalizing that general
statement, we use the following description of separatedness, which is stable under base change and
descent in a completely elementary way.

* `IsSeparated f` means `IsClosedImmersion (pullback.diagonal f)`, i.e. the diagonal is a closed
  immersion.
* The diagonal `Δ = pullback.diagonal f` of any morphism is a *split* monomorphism
  (`Δ ≫ pullback.fst f f = 𝟙 _`).  Hence it is injective (on the underlying spaces) and it is
  automatically surjective on stalks (`surjectiveOnStalks_diagonal` below).
* Consequently
  `IsSeparated f ↔ UniversallyClosed (pullback.diagonal f)`  (`isSeparated_of_universallyClosed_diagonal`
  for the implication needed below, the converse being the instance `IsClosedImmersion → UniversallyClosed`):
  a morphism is a closed immersion iff it is (a) injective, (b) surjective on stalks and (c) a closed
  embedding; for the diagonal (a) and (b) are free, and a universally closed injective map has a
  closed embedding as underlying map (`Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap`).
* `UniversallyClosed` is stable under base change by definition, so it *descends* along any
  surjective, flat and quasi-compact morphism (`MorphismProperty.DescendsAlong @UniversallyClosed`
  in Mathlib), and by the `MorphismProperty.diagonal` descent instance this transfers to
  separatedness: `IsSeparated.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`.

The base change `Spec k' ⟶ Spec k` of a field extension is surjective, flat and quasi-compact, so
separatedness descends along it, which is the statement `isSeparated_of_bc`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

universe u

namespace Work.DescentGeom

open CategoryTheory Limits AlgebraicGeometry

/- Auxiliary lemmas for the descent of separatedness; kept in a namespace of their own so that
they cannot collide with the rest of the area. -/
namespace IsSepDesc

variable {X Y : Scheme}

/-- A morphism with a section is surjective on stalks. -/
theorem surjectiveOnStalks_of_comp_eq_id {X Y : Scheme} {f : X ⟶ Y} {g : Y ⟶ X}
    (h : f ≫ g = 𝟙 X) : SurjectiveOnStalks f := by
  haveI : SurjectiveOnStalks (f ≫ g) := by rw [h]; infer_instance
  exact SurjectiveOnStalks.of_comp f g

/-- The diagonal is surjective on stalks: it is a section of the first projection. -/
theorem surjectiveOnStalks_diagonal (f : X ⟶ Y) :
    SurjectiveOnStalks (pullback.diagonal f) :=
  surjectiveOnStalks_of_comp_eq_id (pullback.diagonal_fst f)

/-- The diagonal is injective on the underlying spaces, since it is a section of the first
projection. -/
theorem injective_diagonal (f : X ⟶ Y) : Function.Injective ⇑(pullback.diagonal f) := by
  intro x y hxy
  have h := congrArg (fun k : X ⟶ X => ⇑k) (pullback.diagonal_fst f)
  simp only [Scheme.Hom.comp_base, Scheme.Hom.id_base] at h
  have hx := congrFun h x
  have hy := congrFun h y
  have hx' : ⇑(pullback.fst f f) (⇑(pullback.diagonal f) x) = x := by simpa using hx
  have hy' : ⇑(pullback.fst f f) (⇑(pullback.diagonal f) y) = y := by simpa using hy
  rw [← hx', ← hy', hxy]

/-- A universally closed morphism of schemes induces a closed map on the underlying spaces. -/
theorem isClosedMap_of_universallyClosed {f : X ⟶ Y} (h : UniversallyClosed f) : IsClosedMap ⇑f :=
  MorphismProperty.universally_le _ f h.universally_isClosedMap

/-- **Universally closed diagonals are closed immersions.**  Since the diagonal is a section, it is
injective and surjective on stalks, so it remains to note that a universally closed morphism whose
underlying map is injective is a closed embedding. -/
theorem isSeparated_of_universallyClosed_diagonal (f : X ⟶ Y)
    [h : UniversallyClosed (pullback.diagonal f)] : IsSeparated f := by
  have hcm : IsClosedMap ⇑(pullback.diagonal f) := isClosedMap_of_universallyClosed h
  have hinj : Function.Injective ⇑(pullback.diagonal f) := injective_diagonal f
  have hce : Topology.IsClosedEmbedding ⇑(pullback.diagonal f) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (pullback.diagonal f).continuous hinj hcm
  haveI := surjectiveOnStalks_diagonal f
  exact IsSeparated.mk (IsClosedImmersion.mk hce)

/-- **Separatedness descends along fpqc covers** (Stacks 02L6 in the form needed here): if a
morphism `f : X ⟶ Z` is surjective, flat and quasi-compact and the base change
`X ×[Z] Y ⟶ X` of `g : Y ⟶ Z` is separated, then `g` is separated. -/
theorem isSeparated_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) := by
  haveI hstable :
      MorphismProperty.IsStableUnderBaseChange
        ((@Surjective : MorphismProperty Scheme) ⊓ (@Flat : MorphismProperty Scheme)) :=
    MorphismProperty.IsStableUnderBaseChange.inf (P := @Surjective) (Q := @Flat)
  haveI hstable' :
      MorphismProperty.IsStableUnderBaseChange
        ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := (@Surjective : MorphismProperty Scheme) ⊓ @Flat) (Q := @QuasiCompact)
  haveI hdiag :
      (MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme)).DescendsAlong
        ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme) :=
    @MorphismProperty.instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange Scheme _ _
      (@UniversallyClosed : MorphismProperty Scheme)
      ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme) inferInstance
      universallyClosed_respectsIso hstable'
  refine MorphismProperty.DescendsAlong.mk' (fun {X Y Z} {f : X ⟶ Z} {g : Y ⟶ Z} _ hf hfst => ?_)
  have h1 : (MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme))
      (pullback.fst f g) := by
    change UniversallyClosed (pullback.diagonal (pullback.fst f g))
    infer_instance
  have h2 : UniversallyClosed (pullback.diagonal g) :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme))
      (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)) hf h1
  exact isSeparated_of_universallyClosed_diagonal g (h := h2)

end IsSepDesc

open IsSepDesc in
/-- **Separatedness descends along a base change of a field.**  If the base change `A_{k'}` of a
`k`-scheme `A` along a field extension `k'/k` is separated over `k'`, then `A` is separated over
`k`.

The cover `Spec k' ⟶ Spec k` is surjective, flat and quasi-compact, so it is an fpqc cover, and
separatedness is fpqc local on the base: `IsSeparated` is `MorphismProperty.diagonal` of the
closed-immersion property, which descends as soon as `UniversallyClosed` does — and for a diagonal
being universally closed is the same as being a closed immersion
(`isSeparated_of_universallyClosed_diagonal`). -/
theorem isSeparated_of_bc {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (A : Work.DescentGeom.Sch k) [AlgebraicGeometry.IsSeparated (Work.DescentGeom.bc k' A).hom] :
    AlgebraicGeometry.IsSeparated A.hom := by
  -- the cover `Spec k' ⟶ Spec k` is an fpqc cover
  haveI hstable :
      MorphismProperty.IsStableUnderBaseChange
        ((@Surjective : MorphismProperty Scheme) ⊓ (@Flat : MorphismProperty Scheme)) :=
    MorphismProperty.IsStableUnderBaseChange.inf (P := @Surjective) (Q := @Flat)
  haveI hstable' :
      MorphismProperty.IsStableUnderBaseChange
        ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := (@Surjective : MorphismProperty Scheme) ⊓ @Flat) (Q := @QuasiCompact)
  -- separatedness, written as `diagonal UniversallyClosed`, descends along such covers
  haveI hdiag :
      (MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme)).DescendsAlong
        ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme) :=
    @MorphismProperty.instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange Scheme _ _
      (@UniversallyClosed : MorphismProperty Scheme)
      ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme) inferInstance
      universallyClosed_respectsIso hstable'
  have hcover : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (Work.Descent.specMap k k') := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  -- the hypothesis at the level of the diagonal of the base change
  have hd : (MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme))
      (pullback.snd A.hom (Work.Descent.specMap k k')) := by
    change UniversallyClosed (pullback.diagonal (Work.DescentGeom.bc k' A).hom)
    infer_instance
  have hmain : UniversallyClosed (pullback.diagonal A.hom) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme))
      (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme))
      (f := A.hom) (g := Work.Descent.specMap k k') hcover hd
  exact IsSepDesc.isSeparated_of_universallyClosed_diagonal A.hom

end Work.DescentGeom
