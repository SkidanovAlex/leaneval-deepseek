import Mathlib
import Submission.Work.GroupChunk.Assembly
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Gluing.Data
import Submission.Work.GroupChunk.Desc.desc_exists
import Submission.Work.GroupChunk.Transitions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.GroupLaw

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open Work.GCBasics
open Work.GroupChunk

noncomputable section

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
  {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]

/-! ## Auxiliary lemmas about the class map `cls`

The group axioms for `mul`, `inv`, `one` are detected by `cls` (`hom_ext_cls`), so we need
to be able to compute `cls` of a point composed with a morphism built out of `mul`, `inv`,
`one` and the Cartesian monoidal structure.  These lemmas do exactly that:
`hom_ext_cls_pt` is `hom_ext_cls` tested on arbitrary field points, `cls_mul_comp` computes
`cls` of `f ≫ mul` via the two coordinates of `f`, and `cls_unit_comp_one` /
`cls_inv_comp` handle the unit and the inverse. -/

/-- `hom_ext_cls` tested on arbitrary field points (not only residue-field points). -/
theorem hom_ext_cls_pt (D : Input C P0) [IsSeparated (GSch D).hom] {Y : Sch K}
    [IsReduced Y.left] {u v : Y ⟶ GSch D}
    (h : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt Y F), D.cls (p ≫ u) = D.cls (p ≫ v)) :
    u = v :=
  Input.hom_ext_cls D u v (fun y => h (resPt Y y))

/-- The class of `f ≫ mul` is the sum of the classes of the two coordinates of `f`. -/
theorem cls_mul_comp (D : Input C P0) (mul : GSch D ⊗ GSch D ⟶ GSch D)
    (hmul : ∀ {F : Type u} [Field F] [Algebra K F] (p q : FPt (GSch D) F),
      D.cls (CartesianMonoidalCategory.liftEquiv (p, q) ≫ mul) = D.cls p + D.cls q)
    {F : Type u} [Field F] [Algebra K F] {Y : Sch K} (f : Y ⟶ GSch D ⊗ GSch D) (p : FPt Y F) :
    D.cls (p ≫ f ≫ mul)
      = D.cls (p ≫ f ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D))
        + D.cls (p ≫ f ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)) := by
  have key : p ≫ f = CartesianMonoidalCategory.liftEquiv
      (p ≫ f ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D),
       p ≫ f ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)) := by
    rw [show CartesianMonoidalCategory.liftEquiv
        (p ≫ f ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D),
         p ≫ f ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D))
        = CartesianMonoidalCategory.lift
          (p ≫ f ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D))
          (p ≫ f ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)) from rfl]
    rw [← Category.assoc, ← Category.assoc]
    exact (CartesianMonoidalCategory.lift_comp_fst_snd (f := p ≫ f)).symm
  rw [← Category.assoc p f mul, key]
  exact hmul _ _

/-- The class of `p ≫ u ≫ one` vanishes for any morphism `u` into the unit object. -/
theorem cls_unit_comp_one (D : Input C P0) (one : 𝟙_ (Sch K) ⟶ GSch D)
    (hone : ∀ {F : Type u} [Field F] [Algebra K F],
      D.cls (CartesianMonoidalCategory.toUnit (specOf K F) ≫ one) = 0)
    {F : Type u} [Field F] [Algebra K F] {Y : Sch K} (p : FPt Y F) (u : Y ⟶ 𝟙_ (Sch K)) :
    D.cls (p ≫ u ≫ one) = 0 := by
  rw [← Category.assoc, show p ≫ u = CartesianMonoidalCategory.toUnit (specOf K F)
    from Work.GroupChunk.toUnit_unique _ _]
  exact hone

/-- The class of `f ≫ inv` is the negative of the class of `f`. -/
theorem cls_inv_comp (D : Input C P0) (inv : GSch D ⟶ GSch D)
    (hinv : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt (GSch D) F),
      D.cls (p ≫ inv) = - D.cls p)
    {F : Type u} [Field F] [Algebra K F] {Y : Sch K} (f : Y ⟶ GSch D) (p : FPt Y F) :
    D.cls (p ≫ f ≫ inv) = - D.cls (p ≫ f) := by
  rw [← Category.assoc]
  exact hinv (p ≫ f)

open CategoryTheory in
open AlgebraicGeometry in
open scoped MonObj in
open scoped MonoidalCategory in
open scoped AlgebraicGeometry in
theorem grpObj_exists {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [IsSeparated (Work.GroupChunk.GSch D).hom]
    (mul : MonoidalCategoryStruct.tensorObj (Work.GroupChunk.GSch D) (Work.GroupChunk.GSch D)
      ⟶ Work.GroupChunk.GSch D)
    (hmul : ∀ {F : Type u} [Field F] [Algebra K F]
      (p q : Work.GCBasics.FPt (Work.GroupChunk.GSch D) F),
      Work.GroupChunk.Input.cls D (CartesianMonoidalCategory.liftEquiv (p, q) ≫ mul) =
        Work.GroupChunk.Input.cls D p + Work.GroupChunk.Input.cls D q)
    (inv : Work.GroupChunk.GSch D ⟶ Work.GroupChunk.GSch D)
    (hinv : ∀ {F : Type u} [Field F] [Algebra K F]
      (p : Work.GCBasics.FPt (Work.GroupChunk.GSch D) F),
      Work.GroupChunk.Input.cls D (p ≫ inv) = - Work.GroupChunk.Input.cls D p)
    (one : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ Work.GroupChunk.GSch D)
    (hone : ∀ {F : Type u} [Field F] [Algebra K F],
      Work.GroupChunk.Input.cls D
        (Work.GroupChunk.toUnit (Work.GCBasics.specOf K F) ≫ one) = 0) :
    ∃ G : GrpObj (Work.GroupChunk.GSch D), G.mul = mul ∧ G.inv = inv ∧ G.one = one := by
  refine ⟨{ one := one, mul := mul, one_mul := ?_, mul_one := ?_, mul_assoc := ?_,
            inv := inv, left_inv := ?_, right_inv := ?_ }, rfl, rfl, rfl⟩
  · -- `one_mul`
    have hmain : (λ_ (GSch D)).inv ≫ (one ▷ GSch D ≫ mul) = 𝟙 (GSch D) := by
      apply hom_ext_cls_pt D
      intro F _ _ p
      rw [Category.comp_id]
      rw [← Category.assoc]
      rw [cls_mul_comp D mul hmul (f := one ▷ GSch D) (p := p ≫ (λ_ (GSch D)).inv)]
      have hfst_eq : (p ≫ (λ_ (GSch D)).inv) ≫ (one ▷ GSch D)
          ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D)
          = p ≫ CartesianMonoidalCategory.toUnit (GSch D) ≫ one := by
        show (p ≫ (λ_ (GSch D)).inv) ≫ (one ⊗ₘ 𝟙 (GSch D))
            ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D)
            = p ≫ CartesianMonoidalCategory.toUnit (GSch D) ≫ one
        rw [CartesianMonoidalCategory.tensorHom_fst, Category.assoc,
          ← Category.assoc (λ_ (GSch D)).inv,
          CartesianMonoidalCategory.leftUnitor_inv_fst]
      have hsnd_eq : (p ≫ (λ_ (GSch D)).inv) ≫ (one ▷ GSch D)
          ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D) = p := by
        show (p ≫ (λ_ (GSch D)).inv) ≫ (one ⊗ₘ 𝟙 (GSch D))
            ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D) = p
        rw [CartesianMonoidalCategory.tensorHom_snd, Category.comp_id]
        rw [Category.assoc, CartesianMonoidalCategory.leftUnitor_inv_snd, Category.comp_id]
      rw [hfst_eq, hsnd_eq,
        cls_unit_comp_one D one hone p (CartesianMonoidalCategory.toUnit (GSch D)), zero_add]
    have hm2 := (Iso.inv_comp_eq (λ_ (GSch D))).mp hmain
    simpa using hm2
  · -- `mul_one`
    have hmain : (ρ_ (GSch D)).inv ≫ ((GSch D ◁ one) ≫ mul) = 𝟙 (GSch D) := by
      apply hom_ext_cls_pt D
      intro F _ _ p
      rw [Category.comp_id]
      rw [← Category.assoc]
      rw [cls_mul_comp D mul hmul (f := GSch D ◁ one) (p := p ≫ (ρ_ (GSch D)).inv)]
      have hfst_eq : (p ≫ (ρ_ (GSch D)).inv) ≫ (GSch D ◁ one)
          ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D) = p := by
        show (p ≫ (ρ_ (GSch D)).inv) ≫ (𝟙 (GSch D) ⊗ₘ one)
            ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D) = p
        rw [CartesianMonoidalCategory.tensorHom_fst, Category.comp_id]
        rw [Category.assoc, CartesianMonoidalCategory.rightUnitor_inv_fst, Category.comp_id]
      have hsnd_eq : (p ≫ (ρ_ (GSch D)).inv) ≫ (GSch D ◁ one)
          ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)
          = p ≫ CartesianMonoidalCategory.toUnit (GSch D) ≫ one := by
        show (p ≫ (ρ_ (GSch D)).inv) ≫ (𝟙 (GSch D) ⊗ₘ one)
            ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)
            = p ≫ CartesianMonoidalCategory.toUnit (GSch D) ≫ one
        rw [CartesianMonoidalCategory.tensorHom_snd]
        rw [← Category.assoc (p ≫ (ρ_ (GSch D)).inv)
              (CartesianMonoidalCategory.snd (GSch D) (𝟙_ (Sch K))) one,
          Category.assoc p (ρ_ (GSch D)).inv
            (CartesianMonoidalCategory.snd (GSch D) (𝟙_ (Sch K))),
          CartesianMonoidalCategory.rightUnitor_inv_snd,
          ← Category.assoc p (CartesianMonoidalCategory.toUnit (GSch D)) one]
      rw [hfst_eq, hsnd_eq,
        cls_unit_comp_one D one hone p (CartesianMonoidalCategory.toUnit (GSch D)), add_zero]
    have hm2 := (Iso.inv_comp_eq (ρ_ (GSch D))).mp hmain
    simpa using hm2
  · -- `mul_assoc`
    apply hom_ext_cls_pt D
    intro F _ _ p
    rw [cls_mul_comp D mul hmul (f := mul ▷ GSch D) (p := p)]
    have hL1 : D.cls (p ≫ (mul ▷ GSch D) ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D))
        = D.cls (p ≫ CartesianMonoidalCategory.fst (GSch D ⊗ GSch D) (GSch D)
              ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D))
          + D.cls (p ≫ CartesianMonoidalCategory.fst (GSch D ⊗ GSch D) (GSch D)
              ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)) := by
      rw [CartesianMonoidalCategory.whiskerRight_fst]
      exact cls_mul_comp D mul hmul
        (f := CartesianMonoidalCategory.fst (GSch D ⊗ GSch D) (GSch D)) (p := p)
    have hL2 : D.cls (p ≫ (mul ▷ GSch D) ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D))
        = D.cls (p ≫ CartesianMonoidalCategory.snd (GSch D ⊗ GSch D) (GSch D)) := by
      rw [CartesianMonoidalCategory.whiskerRight_snd]
    have hR : D.cls (p ≫ (α_ (GSch D) (GSch D) (GSch D)).hom ≫ ((GSch D ◁ mul) ≫ mul))
        = (D.cls (p ≫ CartesianMonoidalCategory.fst (GSch D ⊗ GSch D) (GSch D)
                ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D))
            + D.cls (p ≫ CartesianMonoidalCategory.fst (GSch D ⊗ GSch D) (GSch D)
                ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)))
          + D.cls (p ≫ CartesianMonoidalCategory.snd (GSch D ⊗ GSch D) (GSch D)) := by
      show D.cls ((p ≫ (α_ (GSch D) (GSch D) (GSch D)).hom) ≫ ((GSch D ◁ mul) ≫ mul)) = _
      rw [cls_mul_comp D mul hmul (f := GSch D ◁ mul)
        (p := p ≫ (α_ (GSch D) (GSch D) (GSch D)).hom)]
      have e1 : D.cls ((p ≫ (α_ (GSch D) (GSch D) (GSch D)).hom) ≫ (GSch D ◁ mul)
            ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D))
          = D.cls (p ≫ CartesianMonoidalCategory.fst (GSch D ⊗ GSch D) (GSch D)
                ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D)) := by
        rw [CartesianMonoidalCategory.whiskerLeft_fst, Category.assoc,
          CartesianMonoidalCategory.associator_hom_fst]
      have e2 : D.cls ((p ≫ (α_ (GSch D) (GSch D) (GSch D)).hom) ≫ (GSch D ◁ mul)
            ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D))
          = D.cls (p ≫ CartesianMonoidalCategory.fst (GSch D ⊗ GSch D) (GSch D)
                ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D))
            + D.cls (p ≫ CartesianMonoidalCategory.snd (GSch D ⊗ GSch D) (GSch D)) := by
        rw [CartesianMonoidalCategory.whiskerLeft_snd]
        rw [cls_mul_comp D mul hmul
          (f := CartesianMonoidalCategory.snd (GSch D) (GSch D ⊗ GSch D))
          (p := p ≫ (α_ (GSch D) (GSch D) (GSch D)).hom)]
        have f1 : D.cls ((p ≫ (α_ (GSch D) (GSch D) (GSch D)).hom)
              ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D ⊗ GSch D)
              ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D))
            = D.cls (p ≫ CartesianMonoidalCategory.fst (GSch D ⊗ GSch D) (GSch D)
                ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)) := by
          rw [Category.assoc, CartesianMonoidalCategory.associator_hom_snd_fst]
        have f2 : D.cls ((p ≫ (α_ (GSch D) (GSch D) (GSch D)).hom)
              ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D ⊗ GSch D)
              ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D))
            = D.cls (p ≫ CartesianMonoidalCategory.snd (GSch D ⊗ GSch D) (GSch D)) := by
          rw [Category.assoc, CartesianMonoidalCategory.associator_hom_snd_snd]
        rw [f1, f2]
      rw [e1, e2, ← add_assoc]
    rw [hL1, hL2, hR]
  · -- `left_inv`
    apply hom_ext_cls_pt D
    intro F _ _ p
    rw [cls_mul_comp D mul hmul
      (f := CartesianMonoidalCategory.lift inv (𝟙 (GSch D))) (p := p)]
    have e1 : D.cls (p ≫ CartesianMonoidalCategory.lift inv (𝟙 (GSch D))
        ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D)) = - D.cls p := by
      rw [CartesianMonoidalCategory.lift_fst]
      exact hinv p
    have e2 : D.cls (p ≫ CartesianMonoidalCategory.lift inv (𝟙 (GSch D))
        ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)) = D.cls p := by
      rw [CartesianMonoidalCategory.lift_snd, Category.comp_id]
    rw [e1, e2, cls_unit_comp_one D one hone p (CartesianMonoidalCategory.toUnit (GSch D))]
    exact neg_add_cancel _
  · -- `right_inv`
    apply hom_ext_cls_pt D
    intro F _ _ p
    rw [cls_mul_comp D mul hmul
      (f := CartesianMonoidalCategory.lift (𝟙 (GSch D)) inv) (p := p)]
    have e1 : D.cls (p ≫ CartesianMonoidalCategory.lift (𝟙 (GSch D)) inv
        ≫ CartesianMonoidalCategory.fst (GSch D) (GSch D)) = D.cls p := by
      rw [CartesianMonoidalCategory.lift_fst, Category.comp_id]
    have e2 : D.cls (p ≫ CartesianMonoidalCategory.lift (𝟙 (GSch D)) inv
        ≫ CartesianMonoidalCategory.snd (GSch D) (GSch D)) = - D.cls p := by
      rw [CartesianMonoidalCategory.lift_snd]
      exact hinv p
    rw [e1, e2, cls_unit_comp_one D one hone p (CartesianMonoidalCategory.toUnit (GSch D))]
    exact add_neg_cancel _

end

end Work.GroupChunk.GroupLaw
