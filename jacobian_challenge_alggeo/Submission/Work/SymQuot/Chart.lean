/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Charts of the quotient by a finite group (area SY)

For a scheme `X` with an action of a group `G` and a `G`-invariant affine open subscheme
`U ⊆ X`, the *chart* of `U` is `Spec Γ(X, U)^G`, the spectrum of the ring of invariants of the
sections over `U`.  The quotient `X/G` is obtained by gluing the charts of an invariant affine
open cover of `X`; this file provides the local models and the restriction maps between them.
-/
import Submission.Work.SymQuot.Sections

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

namespace GAction

variable {G : Type u} [Group G] {X : Scheme.{u}} (A : GAction G X)

/-- Restriction of sections along an inclusion of open subschemes. -/
def restrictSections (V U : X.Opens) (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp]
lemma restrictSections_apply (V U : X.Opens) (h : V ≤ U) (s : Γ(X, U)) :
    restrictSections V U h s = X.presheaf.map (homOfLE h).op s := rfl

@[simp]
lemma restrictSections_self (U : X.Opens) (s : Γ(X, U)) : restrictSections U U le_rfl s = s := by
  simp only [restrictSections_apply]
  have h : homOfLE (le_rfl : U ≤ U) = 𝟙 U := Subsingleton.elim _ _
  rw [h, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restriction of sections commutes with the action of `G` on invariant opens. -/
lemma appLE_restrictSections (V U : X.Opens) (h : V ≤ U) (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) (g : G) :
    Scheme.Hom.appLE (A.hom g) U U (le_of_eq (hU g).symm) ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE h).op ≫
        Scheme.Hom.appLE (A.hom g) V V (le_of_eq (hV g).symm) := by
  rw [Scheme.Hom.appLE_map (f := A.hom g) (e := le_of_eq (hU g).symm)
      (i := (homOfLE h).op)]
  rw [Scheme.Hom.map_appLE (f := A.hom g) (e := le_of_eq (hV g).symm)
      (i := (homOfLE h).op)]

/-- Restriction of sections commutes with the action of `G` on invariant opens. -/
lemma restrictSections_sectionHom (V U : X.Opens) (h : V ≤ U) (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) (g : G) :
    (restrictSections V U h).comp (sectionHom A U hU g) =
      (sectionHom A V hV g).comp (restrictSections V U h) :=
  RingHom.ext fun s => congr($(appLE_restrictSections A V U h hU hV g) s)

/-- The invariant elements of the sections over an invariant open. -/
abbrev invariants (U : X.Opens) (hU : A.IsInvariantOpen U) :
    Subring (↥Γ(X, U)) :=
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hU
  FixedPoints.subring Γ(X, U) G

/-- Membership in the invariants, in terms of the action on sections. -/
lemma mem_invariants_iff {U : X.Opens} (hU : A.IsInvariantOpen U) (s : Γ(X, U)) :
    s ∈ invariants A U hU ↔ ∀ g : G, sectionHom A U hU g⁻¹ s = s := by
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hU
  show s ∈ FixedPoints.submonoid G Γ(X, U) ↔ _
  rw [FixedPoints.mem_submonoid]
  exact forall_congr' fun g => Iff.rfl

/-- For `G`-invariant opens `V ≤ U`, the restriction of invariants
`Γ(X,U)^G → Γ(X,V)^G`. -/
def invariantsRes (V U : X.Opens) (h : V ≤ U) (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) : invariants A U hU →+* invariants A V hV :=
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hU
  letI : MulSemiringAction G Γ(X, V) := A.sectionMulSemiringAction V hV
  { toFun := fun s => ⟨restrictSections V U h s.1, by
      rw [mem_invariants_iff]
      intro g
      rw [← RingHom.comp_apply, ← restrictSections_sectionHom A V U h hU hV g⁻¹,
        RingHom.comp_apply, (mem_invariants_iff A hU s.1).mp s.2 g]⟩
    map_one' := Subtype.ext (by simp)
    map_mul' x y := Subtype.ext (by simp)
    map_zero' := Subtype.ext (by simp)
    map_add' x y := Subtype.ext (by simp) }

@[simp]
lemma invariantsRes_apply (V U : X.Opens) (h : V ≤ U) (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) (s : invariants A U hU) :
    ((invariantsRes A V U h hU hV s : invariants A V hV) : Γ(X, V)) =
      restrictSections V U h s.1 := rfl

noncomputable section

/-- The ring of the chart of a `G`-invariant open subscheme `U`. -/
abbrev chartRing (U : X.Opens) (hU : A.IsInvariantOpen U) : CommRingCat.{u} :=
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hU
  .of (FixedPoints.subring Γ(X, U) G)

/-- The *chart* of a `G`-invariant open subscheme `U`: the spectrum of the ring of invariants
of the sections over `U`.  If `U` is affine, this is the local model of the quotient `X/G`. -/
abbrev chart (U : X.Opens) (hU : A.IsInvariantOpen U) : Scheme.{u} :=
  Spec (chartRing A U hU)

/-- The canonical morphism `U ⟶ chart U`, induced by the inclusion of the invariants. -/
def chartMap (U : X.Opens) (hU : A.IsInvariantOpen U) : U.toScheme ⟶ chart A U hU :=
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hU
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Subring.subtype (invariants A U hU)))

/-- The morphism of charts `chart V ⟶ chart U` induced by an inclusion `V ≤ U` of `G`-invariant
opens. -/
def chartRes (V U : X.Opens) (h : V ≤ U) (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) : chart A V hV ⟶ chart A U hU :=
  Spec.map (CommRingCat.ofHom (invariantsRes A V U h hU hV))

lemma chartRes_id (U : X.Opens) (hU : A.IsInvariantOpen U) :
    chartRes A U U le_rfl hU hU = 𝟙 (chart A U hU) := by
  rw [chartRes]
  have h : invariantsRes A U U le_rfl hU hU = RingHom.id (invariants A U hU) := by
    apply RingHom.ext
    intro s
    exact Subtype.ext (by rw [invariantsRes_apply, RingHom.id_apply, restrictSections_self])
  rw [h, show CommRingCat.ofHom (RingHom.id (invariants A U hU)) = 𝟙 _ from rfl]
  exact Spec.map_id _

lemma invariantsRes_comp_subtype (V U : X.Opens) (h : V ≤ U) (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) :
    CommRingCat.ofHom (Subring.subtype (invariants A U hU)) ≫ X.presheaf.map (homOfLE h).op =
      CommRingCat.ofHom (invariantsRes A V U h hU hV) ≫
        CommRingCat.ofHom (Subring.subtype (invariants A V hV)) := by
  ext s
  exact (invariantsRes_apply A V U h hU hV s).symm

/-- Restriction of sections is transitive. -/
lemma restrictSections_comp (W V U : X.Opens) (h₁ : W ≤ V) (h₂ : V ≤ U) (s : Γ(X, U)) :
    restrictSections W V h₁ (restrictSections V U h₂ s) = restrictSections W U (h₁.trans h₂) s := by
  simp only [restrictSections_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1

/-- The maps on invariants are transitive. -/
lemma invariantsRes_comp (W V U : X.Opens) (h₁ : W ≤ V) (h₂ : V ≤ U)
    (hU : A.IsInvariantOpen U) (hV : A.IsInvariantOpen V) (hW : A.IsInvariantOpen W) :
    (invariantsRes A W V h₁ hV hW).comp (invariantsRes A V U h₂ hU hV) =
      invariantsRes A W U (h₁.trans h₂) hU hW := by
  apply RingHom.ext
  intro s
  exact Subtype.ext (by
    rw [RingHom.comp_apply, invariantsRes_apply, invariantsRes_apply, invariantsRes_apply,
      restrictSections_comp])

/-- The chart inclusions are transitive. -/
lemma chartRes_comp (W V U : X.Opens) (h₁ : W ≤ V) (h₂ : V ≤ U) (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) (hW : A.IsInvariantOpen W) :
    chartRes A W V h₁ hV hW ≫ chartRes A V U h₂ hU hV =
      chartRes A W U (h₁.trans h₂) hU hW := by
  rw [chartRes, chartRes, chartRes, ← Spec.map_comp, Spec.map_inj,
    show CommRingCat.ofHom (invariantsRes A V U h₂ hU hV) ≫
        CommRingCat.ofHom (invariantsRes A W V h₁ hV hW)
      = CommRingCat.ofHom ((invariantsRes A W V h₁ hV hW).comp
          (invariantsRes A V U h₂ hU hV)) from rfl,
    invariantsRes_comp A W V U h₁ h₂ hU hV hW]

end

end GAction

end Work.SymQuot
