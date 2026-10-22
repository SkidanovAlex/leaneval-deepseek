import Mathlib
import Submission.Work.ANALYTIC.HICond

/-!
# Fibre powers commute with `X ↦ X ⊗ [0,1]`

The main statement of this file (`Work.ANALYTIC.widePullbackTensorI_isIso`) is the special case for
`LightCondSet` and the light condensed interval `Icond` of a completely general fact:

*in a cartesian monoidal category `C`, for any object `I` and any wide cospan `B ← objs j`
(`j : J`), the canonical comparison map
`(widePullback B objs arrows) ⊗ I ⟶ widePullback (B ⊗ I) (objs · ⊗ I) (arrows · ▷ I)`
is an isomorphism.*

This is proved here as `widePullback_tensor_isIso_general`.  The proof is the explicit
construction of the inverse: a cone over the cospan `B ⊗ I ← objs j ⊗ I` is the same thing as a
cone over `B ← objs j` together with a map into `I`, and since `⊗` is the cartesian product, the
second coordinates of any such cone are forced to agree, so the cone is obtained by pairing the
induced map to the (original) wide pullback with the map into `I`.

The only subtlety is a formal one: `WidePullbackCone.mk` is an opaque definition, so the cone point
of the cone `WidePullbackCone.mk b π h` does not reduce by `rfl` at the transparency levels used by
tactics.  We therefore build the cone as a structure literal (`tensorCone` below), whose cone point
*is* definitionally the given object `W`.
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/-- The wide-pullback cone over the cospan `X ← objs j ⊗ I` (with `X = B ⊗ I`, structure maps
`arrows j ▷ I`), with cone point `W`, given by the data `b`, `π`.

It is written as a structure literal (rather than as `WidePullbackCone.mk b π h`) so that its cone
point is definitionally `W`, and its legs are definitionally `b` and `π j`. -/
abbrev tensorCone (I : C) {J : Type*} {B : C} (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B)
    {W : C} (b : W ⟶ B ⊗ I) (π : ∀ j : J, W ⟶ objs j ⊗ I)
    (h : ∀ j : J, π j ≫ (arrows j ▷ I) = b) : WidePullbackCone (fun j => arrows j ▷ I) :=
  { pt := W, π := (WidePullbackShape.mkCone b π h).π }

@[simp]
lemma tensorCone_base (I : C) {J : Type*} {B : C} (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B)
    {W : C} (b : W ⟶ B ⊗ I) (π : ∀ j : J, W ⟶ objs j ⊗ I)
    (h : ∀ j : J, π j ≫ (arrows j ▷ I) = b) : (tensorCone I objs arrows b π h).base = b := rfl

@[simp]
lemma tensorCone_π (I : C) {J : Type*} {B : C} (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B)
    {W : C} (b : W ⟶ B ⊗ I) (π : ∀ j : J, W ⟶ objs j ⊗ I)
    (h : ∀ j : J, π j ≫ (arrows j ▷ I) = b) (j : J) :
    (tensorCone I objs arrows b π h).π j = π j := rfl

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory Limits MonoidalCategory in
/-- **`X ↦ X ⊗ I` commutes with wide pullbacks.**  In a cartesian monoidal category `C`, for a wide
cospan `B ← objs j` (`j : J`) and an object `I`, the canonical map
`(widePullback B objs arrows) ⊗ I ⟶ widePullback (B ⊗ I) (objs · ⊗ I) (arrows · ▷ I)`
given by `WidePullback.lift (base ▷ I) (π j ▷ I)` is an isomorphism. -/
theorem widePullback_tensor_isIso_general (I : C) {J : Type*} {B : C} (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B) [HasWidePullback B objs arrows]
    [HasWidePullback (B ⊗ I) (fun j => objs j ⊗ I) (fun j => arrows j ▷ I)]
    (w : ∀ j : J, (WidePullback.π arrows j ▷ I) ≫ (arrows j ▷ I) = WidePullback.base arrows ▷ I) :
    IsIso (WidePullback.lift (WidePullback.base arrows ▷ I)
      (fun j => WidePullback.π arrows j ▷ I) w) := by
  -- The comparison cone (with cone point `(widePullback …) ⊗ I`) is a limit cone.
  have hs : IsLimit (tensorCone I objs arrows (WidePullback.base arrows ▷ I)
      (fun j => WidePullback.π arrows j ▷ I) w) := by
    refine WidePullbackCone.IsLimit.mk _ (fun t => CartesianMonoidalCategory.lift ?_ ?_) ?_ ?_ ?_
    · -- first component: the map to the wide pullback induced by projecting to `B` and the `objs j`
      exact WidePullback.lift (t.base ≫ CartesianMonoidalCategory.fst B I)
        (fun j => t.π j ≫ CartesianMonoidalCategory.fst (objs j) I) (by
          intro j
          rw [Category.assoc, ← CartesianMonoidalCategory.whiskerRight_fst (arrows j) I,
              ← Category.assoc, WidePullbackCone.condition])
    · -- second component: the (forced) map into `I`
      exact t.base ≫ CartesianMonoidalCategory.snd B I
    · -- the cone structure map is a morphism of cones
      intro t
      simp only [tensorCone_base]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst, ← Category.assoc,
          CartesianMonoidalCategory.lift_fst, WidePullback.lift_base]
      · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
          CartesianMonoidalCategory.lift_snd]
    · intro t i
      simp only [tensorCone_π]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst, ← Category.assoc,
          CartesianMonoidalCategory.lift_fst, WidePullback.lift_π]
      · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
          CartesianMonoidalCategory.lift_snd, ← WidePullbackCone.condition t i, Category.assoc,
          CartesianMonoidalCategory.whiskerRight_snd]
    · -- uniqueness
      intro t m hb hπ
      simp only [tensorCone_base] at hb
      have hπ' : ∀ i, m ≫ (WidePullback.π arrows i ▷ I) = t.π i := fun i => by
        simpa only [tensorCone_π] using hπ i
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [CartesianMonoidalCategory.lift_fst]
        apply WidePullback.hom_ext
        · intro j
          rw [Category.assoc,
              ← CartesianMonoidalCategory.whiskerRight_fst (WidePullback.π arrows j) I,
              ← Category.assoc, hπ' j, WidePullback.lift_π]
        · rw [Category.assoc,
              ← CartesianMonoidalCategory.whiskerRight_fst (WidePullback.base arrows) I,
              ← Category.assoc, hb, WidePullback.lift_base]
      · rw [CartesianMonoidalCategory.lift_snd, ← hb, Category.assoc,
          CartesianMonoidalCategory.whiskerRight_snd]
  -- The comparison map is the cone morphism from this limit cone to the canonical limit cone.
  have hT : IsLimit (limit.cone (WidePullbackShape.wideCospan (B ⊗ I)
      (fun j => objs j ⊗ I) (fun j => arrows j ▷ I))) := limit.isLimit _
  have hiff : (IsLimit.conePointUniqueUpToIso hs hT).hom = WidePullback.lift
      (WidePullback.base arrows ▷ I) (fun j => WidePullback.π arrows j ▷ I) w := by
    apply WidePullback.hom_ext
    · intro j
      rw [WidePullback.lift_π]
      change (hs.conePointUniqueUpToIso hT).hom
          ≫ (Cone.π (limit.cone (WidePullbackShape.wideCospan (B ⊗ I) (fun j => objs j ⊗ I)
              (fun j => arrows j ▷ I)))).app (Option.some j) = WidePullback.π arrows j ▷ I
      rw [IsLimit.conePointUniqueUpToIso_hom_comp]
      rfl
    · rw [WidePullback.lift_base]
      change (hs.conePointUniqueUpToIso hT).hom
          ≫ (Cone.π (limit.cone (WidePullbackShape.wideCospan (B ⊗ I) (fun j => objs j ⊗ I)
              (fun j => arrows j ▷ I)))).app Option.none = WidePullback.base arrows ▷ I
      rw [IsLimit.conePointUniqueUpToIso_hom_comp]
      rfl
  rw [← hiff]
  exact Iso.isIso_hom _

end General

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed in
/-- **Fibre powers commute with `X ↦ X ⊗ [0,1]`.**  For a wide cospan `Z ← F i` (`i : Fin n`), the
canonical map `(widePullback Z F g) ⊗ Icond ⟶ widePullback (Z ⊗ Icond) (F · ⊗ Icond) (g · ▷ Icond)`
given by `WidePullback.lift (base ▷ Icond) (π i ▷ Icond)` is an isomorphism.

The shape is nonempty and connected, so a cone over the cospan `(Z ⊗ Icond) ← (F i ⊗ Icond)` is the
same thing as a cone over `Z ← F i` together with a map into `Icond`: in `LightCondSet` the
monoidal structure is cartesian, so `f ▷ Icond` is `f` on the first coordinate and the identity on
the second, and the second coordinates of all the legs are forced to agree.  (`n = 0` is the case
of a single vertex: both sides are `Z ⊗ Icond`.) -/
theorem widePullbackTensorI_isIso {n : ℕ} {F : Fin n → LightCondSet.{0}} {Z : LightCondSet.{0}}
    (g : ∀ i : Fin n, F i ⟶ Z) :
    IsIso (Limits.WidePullback.lift (Limits.WidePullback.base g ▷ Work.ANALYTIC.Icond)
      (fun i => Limits.WidePullback.π g i ▷ Work.ANALYTIC.Icond)
      (by intro j; rw [← MonoidalCategory.comp_whiskerRight, Limits.WidePullback.π_arrow]) :
        Limits.widePullback Z F g ⊗ Work.ANALYTIC.Icond ⟶
        Limits.widePullback (Z ⊗ Work.ANALYTIC.Icond) (fun i => F i ⊗ Work.ANALYTIC.Icond)
          (fun i => g i ▷ Work.ANALYTIC.Icond)) := by
  refine widePullback_tensor_isIso_general (C := LightCondSet.{0}) Work.ANALYTIC.Icond F g ?_

end Work.ANALYTIC
