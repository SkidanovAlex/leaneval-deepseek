import Mathlib
import Submission.Work.Stems.Cone

/-!
# The cofibre of a map `F → E`, and the "coned off fibre" of a fibration

For a continuous map `ι : F → E` the **cofibre** `E ∪_F CF` is the pushout of `ι` and the inclusion
of `F` as the base of the cone on `F`.  Realised as a quotient of `E ⊕ Cone F`.

This is the space used in the "cofibre + Blakers–Massey + homological Whitehead" proof of Serre's
theorem in the stable range: for a Hurewicz fibration `p : E → B` with fibre `F`, the collapse
`E ∪_F CF → B` is a `π`-isomorphism in the range `≤ 2·(conn F)`, whence a homology isomorphism in the
same range by the range Whitehead theorem, and `H_*(E,F) ≅ H_*(E ∪_F CF, CF)` by excision.

## Main names

* `Work.RatHurewicz.cofibreRel`, `cofibre` — the space;
* `cofibreIncl`, `cofibreInclCone` — the two structure maps;
* `cofibreIncl_coneIncl` — the gluing relation;
* `cofibreCollapse` — the collapse `cofibre ι → B` when `p ∘ ι` is constant;
* `cofibreInclConeApex` — the cone point.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.RatHurewicz

noncomputable section

variable {E F B : Type}

/-- The gluing relation defining the cofibre of `ι : F → E`: the base point `coneIncl x` of the cone
on `F` is glued to `ι x ∈ E`. -/
def cofibreRel [TopologicalSpace E] [TopologicalSpace F] (ι : C(F, E)) :
    (E ⊕ Work.Stems.Cone F) → (E ⊕ Work.Stems.Cone F) → Prop :=
  fun a b => ∃ x : F, a = Sum.inl (ι x) ∧ b = Sum.inr (Work.Stems.coneIncl x)

/-- **The cofibre** `E ∪_F CF` of `ι : F → E`. -/
abbrev cofibre [TopologicalSpace E] [TopologicalSpace F] (ι : C(F, E)) : Type _ :=
  Quotient (Relation.EqvGen.setoid (cofibreRel ι))

instance instTopologicalSpaceCofibre [TopologicalSpace E] [TopologicalSpace F] (ι : C(F, E)) :
    TopologicalSpace (cofibre ι) :=
  inferInstanceAs (TopologicalSpace (Quotient (Relation.EqvGen.setoid (cofibreRel ι))))

/-- The inclusion `E → E ∪_F CF`. -/
def cofibreIncl [TopologicalSpace E] [TopologicalSpace F] (ι : C(F, E)) : C(E, cofibre ι) where
  toFun x := Quotient.mk'' (Sum.inl x)
  continuous_toFun := continuous_quotient_mk'.comp continuous_inl

/-- The inclusion `CF → E ∪_F CF` of the cone. -/
def cofibreInclCone [TopologicalSpace E] [TopologicalSpace F] (ι : C(F, E)) :
    C(Work.Stems.Cone F, cofibre ι) where
  toFun y := Quotient.mk'' (Sum.inr y)
  continuous_toFun := continuous_quotient_mk'.comp continuous_inr

/-- The apex of the cone, inside the cofibre. -/
def cofibreApex [TopologicalSpace E] [TopologicalSpace F] (ι : C(F, E)) (x : F) : cofibre ι :=
  cofibreInclCone ι (Work.Stems.coneApex x)

/-- **The gluing relation**: the base of the cone is glued to `F ⊂ E`. -/
theorem cofibreIncl_coneIncl [TopologicalSpace E] [TopologicalSpace F] (ι : C(F, E)) (x : F) :
    cofibreIncl ι (ι x) = cofibreInclCone ι (Work.Stems.coneIncl x) :=
  Quotient.sound (Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩)

/-- The collapse function `E ⊕ CF → B` induced by `p : E → B` constant on the image of `ι`. -/
def cofibreGlue [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (ι : C(F, E)) (p : C(E, B)) (b : B) : E ⊕ Work.Stems.Cone F → B :=
  Sum.elim (⇑p) (fun _ : Work.Stems.Cone F => b)

/-- The collapse function is continuous. -/
theorem continuous_cofibreGlue [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (ι : C(F, E)) (p : C(E, B)) (b : B) : Continuous (cofibreGlue ι p b) :=
  p.continuous.sumElim (continuous_const : Continuous fun _ : Work.Stems.Cone F => b)

/-- The collapse function respects the gluing relation when `p ∘ ι` is constant. -/
theorem cofibreGlue_rel [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (ι : C(F, E)) (p : C(E, B)) (b : B) (hp : ∀ x, p (ι x) = b) :
    ∀ a b' : E ⊕ Work.Stems.Cone F,
      Relation.EqvGen (cofibreRel ι) a b' → cofibreGlue ι p b a = cofibreGlue ι p b b' := by
  have hgen : ∀ a b' : E ⊕ Work.Stems.Cone F, cofibreRel ι a b' →
      cofibreGlue ι p b a = cofibreGlue ι p b b' := by
    rintro a b' ⟨x, rfl, rfl⟩
    change p (ι x) = b
    exact hp x
  intro a b' hab
  induction hab with
  | rel x y h => exact hgen x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The collapse `E ∪_F CF → B`** induced by `p : E → B` when `p` is constant on the image of
`ι` (the case of interest: `ι` the inclusion of the fibre of a fibration over `b₀`). -/
def cofibreCollapse [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (ι : C(F, E)) (p : C(E, B)) (b : B) (hp : ∀ x, p (ι x) = b) : C(cofibre ι, B) where
  toFun := Quotient.lift (s := Relation.EqvGen.setoid (cofibreRel ι))
    (cofibreGlue ι p b) (cofibreGlue_rel ι p b hp)
  continuous_toFun := (continuous_cofibreGlue ι p b).quotient_lift
    (s := Relation.EqvGen.setoid (cofibreRel ι)) (cofibreGlue_rel ι p b hp)

@[simp]
theorem cofibreCollapse_incl [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (ι : C(F, E)) (p : C(E, B)) (b : B) (hp : ∀ x, p (ι x) = b) (x : E) :
    cofibreCollapse ι p b hp (cofibreIncl ι x) = p x := by
  show Quotient.lift (s := Relation.EqvGen.setoid (cofibreRel ι))
    (cofibreGlue ι p b) (cofibreGlue_rel ι p b hp) (Quotient.mk'' (Sum.inl x)) = p x
  exact Quotient.lift_mk _ _ _

@[simp]
theorem cofibreCollapse_cone [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    (ι : C(F, E)) (p : C(E, B)) (b : B) (hp : ∀ x, p (ι x) = b) (y : Work.Stems.Cone F) :
    cofibreCollapse ι p b hp (cofibreInclCone ι y) = b := by
  show Quotient.lift (s := Relation.EqvGen.setoid (cofibreRel ι))
    (cofibreGlue ι p b) (cofibreGlue_rel ι p b hp) (Quotient.mk'' (Sum.inr y)) = b
  exact Quotient.lift_mk _ _ _

end

end Work.RatHurewicz
