import Mathlib

/-!
# The `PresentedGroup` model of a union of two `2`-complexes

This file contains the definitions used by `presentedGroup_union_amalgam`, the finite form of the
Seifert--van Kampen theorem in the model of `2`-complexes as "generator types with relator sets"
(so that `π₁` is `PresentedGroup`).  It has no `sorry`.

* `presentedMap g h : PresentedGroup S →* PresentedGroup T` is the map induced by a map `g` of
  generator types that sends relators to relators; `presentedMap_of` computes it on generators and
  `presentedGroup_hom_ext` lets one prove equalities of such maps on generators;
* `fg_map_map`, `fg_lift_comp_map` are the compatibility of `FreeGroup.map` and `FreeGroup.lift`;
* for edge sets `E₁ E₂ ⊆ E` of a `2`-complex `Γ = A ∪ B`: `incVal E₁ : ↥E₁ → E` is the inclusion,
  `inc₁`, `inc₂` the inclusions of `↥(E₁ ∩ E₂)` into `↥E₁`, `↥E₂`, `UGRel E₁ E₂ S₁ S₂` is the
  relator set of `Γ` (the union of the images of the relator sets of `A` and `B`), `UGFam` the
  family of vertex groups (`false` = `π₁ A`, `true` = `π₁ B`) and `UGFamPhi` the family of
  amalgamating maps out of `π₁(A ∩ B)`.

With `presentedGroup_union_amalgam` this gives the theorem that is missing from Mathlib and from this
workspace, and that is needed for the residual case of `Work.OROneRel.magnusStepCase2`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

/-- `FreeGroup.map` is compatible with composition. -/
theorem fg_map_map {A B C : Type*} (g : A → B) (g' : B → C) (x : FreeGroup A) :
    FreeGroup.map g' (FreeGroup.map g x) = FreeGroup.map (fun a => g' (g a)) x := by
  induction x using FreeGroup.induction_on with
  | one => simp
  | of a => simp
  | inv_of a ih => rw [map_inv, map_inv, ih, map_inv]
  | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb, map_mul]

/-- `FreeGroup.lift` is compatible with `FreeGroup.map`. -/
theorem fg_lift_comp_map {A B : Type*} {M : Type*} [Group M] (g : A → B) (f : B → M) :
    (FreeGroup.lift f).comp (FreeGroup.map g) = FreeGroup.lift (fun a => f (g a)) := by
  refine FreeGroup.ext_hom _ _ fun a => ?_
  rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]

/-! ## The map of presented groups induced by a map of generators -/

/-- The homomorphism of presented groups induced by a map of generator types that sends relators to
relators. -/
noncomputable def presentedMap {A B : Type*} (g : A → B) {S : Set (FreeGroup A)}
    {T : Set (FreeGroup B)} (h : FreeGroup.map g '' S ⊆ T) :
    PresentedGroup S →* PresentedGroup T :=
  PresentedGroup.toGroup (rels := S) (f := fun a => PresentedGroup.of (g a)) (by
    intro r hr
    have hlift : FreeGroup.lift (fun a => PresentedGroup.of (g a)) =
        (PresentedGroup.mk T).comp (FreeGroup.map g) := by
      refine FreeGroup.ext_hom _ _ fun a => ?_
      rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]
      rfl
    rw [hlift, MonoidHom.comp_apply]
    exact PresentedGroup.one_of_mem (h ⟨r, hr, rfl⟩))

@[simp] theorem presentedMap_of {A B : Type*} (g : A → B) {S : Set (FreeGroup A)}
    {T : Set (FreeGroup B)} (h : FreeGroup.map g '' S ⊆ T) (a : A) :
    presentedMap g h (PresentedGroup.of a) = PresentedGroup.of (g a) :=
  PresentedGroup.toGroup.of _ (x := a)

/-- Two homomorphisms out of a presented group that agree on the generators agree. -/
theorem presentedGroup_hom_ext {A : Type*} {S : Set (FreeGroup A)} {P : Type*} [Group P]
    {f g : PresentedGroup S →* P}
    (h : ∀ a : A, f (PresentedGroup.of a) = g (PresentedGroup.of a)) : f = g := by
  refine MonoidHom.ext fun x => ?_
  refine PresentedGroup.induction_on (C := fun y => f y = g y) x ?_
  intro z
  have hz : ∀ w : FreeGroup A, f ((PresentedGroup.mk S) w) = g ((PresentedGroup.mk S) w) := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => simp
    | of a => exact h a
    | inv_of a ih => simpa only [map_inv] using congrArg Inv.inv ih
    | mul a b iha ihb =>
        simpa only [map_mul] using congrArg₂ (f := fun x y => x * y) iha ihb
  exact hz z

/-! ## The union/amalgam theorem -/

section Amalgam

variable {E : Type u}

/-- The inclusion `↥E₁ → E`. -/
def incVal (E₁ : Set E) : ↥E₁ → E := Subtype.val

/-- The inclusion `↥(E₁ ∩ E₂) → ↥E₁`. -/
def inc₁ (E₁ E₂ : Set E) : ↥(E₁ ∩ E₂) → ↥E₁ := fun x => ⟨x.1, x.2.1⟩

/-- The inclusion `↥(E₁ ∩ E₂) → ↥E₂`. -/
def inc₂ (E₁ E₂ : Set E) : ↥(E₁ ∩ E₂) → ↥E₂ := fun x => ⟨x.1, x.2.2⟩

variable (E₁ E₂ : Set E) (S₁ : Set (FreeGroup ↥E₁)) (S₂ : Set (FreeGroup ↥E₂))
  (S₀ : Set (FreeGroup ↥(E₁ ∩ E₂)))

/-- The relator set of the union of the two `2`-complexes. -/
def UGRel : Set (FreeGroup E) :=
  FreeGroup.map (incVal E₁) '' S₁ ∪ FreeGroup.map (incVal E₂) '' S₂

/-- The family of vertex groups (indexed by `Bool`: `false` is the first `2`-complex, `true` the
second). -/
def UGFam : Bool → Type u
  | false => PresentedGroup S₁
  | true => PresentedGroup S₂

instance instUGFam (i : Bool) : Group (UGFam E₁ E₂ S₁ S₂ i) :=
  match i with
  | false => inferInstanceAs (Group (PresentedGroup S₁))
  | true => inferInstanceAs (Group (PresentedGroup S₂))

variable (h₁ : FreeGroup.map (inc₁ E₁ E₂) '' S₀ ⊆ S₁)
  (h₂ : FreeGroup.map (inc₂ E₁ E₂) '' S₀ ⊆ S₂)

/-- The family of amalgamating homomorphisms `π₁(A ∩ B) → π₁(A)`, `π₁(A ∩ B) → π₁(B)`. -/
noncomputable def UGFamPhi : (i : Bool) → PresentedGroup S₀ →* UGFam E₁ E₂ S₁ S₂ i
  | false => presentedMap (inc₁ E₁ E₂) h₁
  | true => presentedMap (inc₂ E₁ E₂) h₂

end Amalgam

end Work.OROneRel
