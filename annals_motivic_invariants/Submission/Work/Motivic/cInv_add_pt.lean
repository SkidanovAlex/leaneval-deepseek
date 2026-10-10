import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.cInv_add_defs
import Submission.Work.Motivic.hom_eq_of_toRationalMap_eq
import Submission.Work.Motivic.coheight_toPartialMap_hom
import Submission.Work.Motivic.resEquiv_of_morphism

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The point map `phiPt` of a birational map: basic properties

This file develops, on top of the shared definitions in `Submission/Work/Motivic/cInv_add_defs.lean`,
the first properties of the point map `phiPt φ : {x // IsIsoAt φ x} → Y`:

* `phiPt_eq_of_rep` — well-definedness, i.e. the value at `x` does not depend on the chosen
  representing partial isomorphism;
* `phiPt_apply` — the value is the evaluation of the chosen representative;
* `coheight_phiPt` — `phiPt` preserves the codimension.
-/

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- A partial isomorphism representing an `𝕜`-birational map is itself over `𝕜`. -/
lemma partialIso_isOver_of_toRationalMap_eq {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [Variety 𝕜 X] [Variety 𝕜 Y] (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))]
    (i : X.PartialIso Y) (hi : i.toRationalMap = φ.hom) :
    i.toPartialMap.IsOver (Spec (.of 𝕜)) := by
  rw [← PartialMap.isOver_toRationalMap_iff_of_isSeparated (S := Spec (.of 𝕜))]
  rw [show i.toPartialMap.toRationalMap = φ.hom from hi]
  infer_instance

/-- `phiPt φ p` is the evaluation of any partial isomorphism representing `φ` whose source
contains the point. -/
lemma phiPt_eq_of_rep {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))] (x : X) (h : IsIsoAt φ x)
    (i : X.PartialIso Y) (hi : i.toRationalMap = φ.hom) (hx : x ∈ i.source) :
    phiPt φ ⟨x, h⟩ = i.target.ι (i.iso.hom ⟨x, hx⟩) := by
  haveI hiov : i.toPartialMap.IsOver (Spec (.of 𝕜)) := partialIso_isOver_of_toRationalMap_eq φ i hi
  have hcov : h.choose.toPartialMap.IsOver (Spec (.of 𝕜)) :=
    partialIso_isOver_of_toRationalMap_eq φ h.choose h.choose_spec.2
  have hmain := hom_eq_of_toRationalMap_eq (S := Spec (.of 𝕜)) (i := h.choose) (j := i)
    (h := h.choose_spec.2.trans hi.symm) h.choose_spec.1 hx
  have hleft : (h.choose.toPartialMap.hom ⟨x, h.choose_spec.1⟩ : Y) =
      phiPt φ ⟨x, h⟩ := by
    rw [show phiPt φ ⟨x, h⟩ =
      h.choose.target.ι (h.choose.iso.hom ⟨x, h.choose_spec.1⟩) from rfl]
    exact Scheme.Hom.comp_apply h.choose.iso.hom h.choose.target.ι ⟨x, h.choose_spec.1⟩
  have hright : (i.toPartialMap.hom ⟨x, hx⟩ : Y) = i.target.ι (i.iso.hom ⟨x, hx⟩) :=
    Scheme.Hom.comp_apply i.iso.hom i.target.ι ⟨x, hx⟩
  rw [← hleft, ← hright]
  exact hmain

/-- The value of `phiPt` at a point is the evaluation of the chosen representing partial
isomorphism. -/
lemma phiPt_apply {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) (p : {x : X // IsIsoAt φ x}) :
    phiPt φ p = p.2.choose.target.ι (p.2.choose.iso.hom ⟨p.1, p.2.choose_spec.1⟩) := rfl

/-- `phiPt` preserves the codimension of a point. -/
lemma coheight_phiPt {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) (p : {x : X // IsIsoAt φ x}) :
    coheight (phiPt φ p) = coheight p.1 := by
  rw [phiPt_apply]
  exact coheight_toPartialMap_hom p.2.choose p.2.choose_spec.1

/- Auxiliary lemmas for `phiPt_symm`, kept in their own namespace so that they cannot clash with
the parallel development of the same facts for `Submission/Work/Motivic/cInv_mul_defs.lean`. -/
namespace CAdd

/-- For an isomorphism of schemes `e : A ≅ B` and a point `p`, `e.inv (e.hom p) = p`. -/
lemma iso_inv_hom_apply {A B : Scheme.{0}} (e : A ≅ B) (p : A) : e.inv (e.hom p) = p := by
  have h := congrArg (fun (f : A ⟶ A) => f.base p) e.hom_inv_id
  simpa using h

/-- The inverse of a partial isomorphism, evaluated at the image of a point of its source. -/
lemma symm_toPartialMap_hom_iso_hom {X Y : Scheme.{0}} (i : X.PartialIso Y) (p : ↥i.source) :
    i.symm.toPartialMap.hom (i.iso.hom p) = i.source.ι p := by
  show i.source.ι (i.iso.inv (i.iso.hom p)) = i.source.ι p
  congr 1
  exact iso_inv_hom_apply i.iso p

/-- The inverse of a partial isomorphism, evaluated at the image of `x`. -/
lemma symm_toPartialMap_hom_target {X Y : Scheme.{0}} (i : X.PartialIso Y) {x : X}
    (hxi : x ∈ i.source) {y : Y} (hy : y ∈ i.target)
    (hy' : y = i.target.ι (i.iso.hom ⟨x, hxi⟩)) :
    i.symm.toPartialMap.hom ⟨y, hy⟩ = x := by
  have he : (⟨y, hy⟩ : ↥i.symm.toPartialMap.domain) = i.iso.hom ⟨x, hxi⟩ := Subtype.ext hy'
  rw [he, symm_toPartialMap_hom_iso_hom]
  rfl

/-- The inverse of a partial isomorphism, evaluated at the image of a point of its source. -/
lemma symm_iso_apply_point {X Y : Scheme.{0}} (i : X.PartialIso Y) (p : ↥i.source)
    {y : Y} (hy : y ∈ i.target) (hy' : y = i.target.ι (i.iso.hom p)) :
    i.symm.target.ι (i.symm.iso.hom ⟨y, hy⟩) = i.source.ι p := by
  have he : (⟨y, hy⟩ : ↥i.symm.source) = i.iso.hom p := Subtype.ext hy'
  rw [he]
  show i.source.ι (i.iso.inv (i.iso.hom p)) = i.source.ι p
  congr 1
  exact iso_inv_hom_apply i.iso p

/-- The inverse partial isomorphism represents the inverse rational map. -/
lemma symm_toRationalMap {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    {φ : X.BirationalMap Y} (i : X.PartialIso Y) (h : i.toRationalMap = φ.hom) :
    i.symm.toRationalMap = φ.inv := by
  have h1 : i.toBirationalMap = φ :=
    BirationalMap.ext _ _ (by rwa [Scheme.PartialIso.toBirationalMap_hom])
  rw [← h1]
  rfl

end CAdd

/-- The point map of `φ` and of `φ.symm` are mutually inverse. -/
theorem phiPt_symm {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))] (p : {x : X // IsIsoAt φ x}) :
    ∃ (h : IsIsoAt φ.symm (phiPt φ p)), phiPt φ.symm ⟨phiPt φ p, h⟩ = p.1 := by
  haveI hsymm : φ.symm.IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs (φ.inv.IsOver (Spec (.of 𝕜)))
  have hmem : phiPt φ p ∈ p.2.choose.target := by
    rw [phiPt_apply]
    exact (p.2.choose.iso.hom ⟨p.1, p.2.choose_spec.1⟩).2
  have hsym : p.2.choose.symm.toRationalMap = φ.inv :=
    CAdd.symm_toRationalMap p.2.choose p.2.choose_spec.2
  refine ⟨⟨p.2.choose.symm, hmem, hsym⟩, ?_⟩
  have hcoe : phiPt φ.symm ⟨phiPt φ p, (⟨p.2.choose.symm, hmem, hsym⟩ : IsIsoAt φ.symm (phiPt φ p))⟩
      = p.2.choose.symm.target.ι (p.2.choose.symm.iso.hom ⟨phiPt φ p, hmem⟩) :=
    phiPt_eq_of_rep (𝕜 := 𝕜) (X := Y) (Y := X) (φ := φ.symm) (x := phiPt φ p)
      (h := ⟨p.2.choose.symm, hmem, hsym⟩) (i := p.2.choose.symm) hsym hmem
  rw [hcoe]
  exact CAdd.symm_iso_apply_point p.2.choose ⟨p.1, p.2.choose_spec.1⟩ hmem
    (phiPt_apply (φ := φ) p)

/-- For a birational map `φ` over `𝕜` which is an isomorphism at `x`, the residue field of `φ x`
is isomorphic to that of `x` as a `𝕜`-algebra. -/
theorem ResEquiv_phiPt {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))] (p : {x : X // IsIsoAt φ x}) :
    ResEquiv 𝕜 p.1 (phiPt φ p) := by
  set i : X.PartialIso Y := p.2.choose with hi
  have hx : p.1 ∈ i.source := p.2.choose_spec.1
  have hrep : i.toRationalMap = φ.hom := p.2.choose_spec.2
  haveI hov : i.toPartialMap.IsOver (Spec (.of 𝕜)) :=
    partialIso_isOver_of_toRationalMap_eq φ i hrep
  have hmov : (i.iso.hom ≫ i.target.ι) ≫ (Y ↘ Spec (.of 𝕜)) =
      i.source.ι ≫ (X ↘ Spec (.of 𝕜)) := hov.comp_over
  have hsrc : i.source.ι ≫ (X ↘ Spec (.of 𝕜)) = (i.source.toScheme ↘ Spec (.of 𝕜)) := by
    rw [← Scheme.Hom.isOver_iff]; infer_instance
  have htgt : i.target.ι ≫ (Y ↘ Spec (.of 𝕜)) = (i.target.toScheme ↘ Spec (.of 𝕜)) := by
    rw [← Scheme.Hom.isOver_iff]; infer_instance
  have hiso : i.iso.hom ≫ (i.target.toScheme ↘ Spec (.of 𝕜)) =
      (i.source.toScheme ↘ Spec (.of 𝕜)) := by
    rw [← htgt, ← Category.assoc, hmov, hsrc]
  set x' : i.source.toScheme := ⟨p.1, hx⟩ with hx'
  have h1 : ResEquiv 𝕜 p.1 x' := resEquiv_of_morphism (f := i.source.ι) hsrc x'
  have h2 : ResEquiv 𝕜 (i.iso.hom x') x' := resEquiv_of_morphism (f := i.iso.hom) hiso x'
  have h3 : ResEquiv 𝕜 (phiPt φ p) (i.iso.hom x') :=
    resEquiv_of_morphism (f := i.target.ι) htgt (i.iso.hom x')
  exact ResEquiv.trans (ResEquiv.trans h1 (ResEquiv.symm h2)) (ResEquiv.symm h3)

end Work.Motivic
