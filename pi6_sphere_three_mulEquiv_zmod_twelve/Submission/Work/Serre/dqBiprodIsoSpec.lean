import Mathlib
import Submission.Work.Serre.RatMVDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `DQ` carries a binary biproduct of `ℤ`-chain complexes to the biproduct of the images

`DQ C = dualComplex ℚ (IntRatCM.obj C)` is the `ℚ`-dual of the base change of a `ℤ`-chain complex
(`Submission/Work/Serre/RatMVDefs.lean`), and `dqMap φ : DQ D ⟶ DQ C` is its contravariant action
on a chain map `φ : C ⟶ D`.  Since `DQ` is a (contravariant, additive) functor into a preadditive
category, it sends the biproduct `C ⊞ D` to the biproduct `DQ C ⊞ DQ D`, the comparison maps being
the transpose of the two inclusions and of the two projections.

The statement `dqBiprodIsoSpec` records the two comparison maps explicitly:
`biprod.lift (dqMap inl) (dqMap inr)` and `biprod.desc (dqMap fst) (dqMap snd)` are mutually
inverse.  The relevant biproduct identities are proved here once and for all in
`biprod_desc_lift_eq_id`; the additivity `dqMap_add` of `dqMap` (which expresses the fact that the
total map `fst ≫ inl + snd ≫ inr` is the identity) supplies the `hom_inv_id` direction.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

/-- **`dqMap` is additive**: it is the action on morphisms of the additive contravariant functor
`DQ`. -/
theorem dqMap_add {C D : ChainComplex (ModuleCat Int) Nat} (f g : C ⟶ D) :
    dqMap (f + g) = dqMap f + dqMap g := by
  have h : Work.StemsB.IntRatCM.map (f + g)
      = Work.StemsB.IntRatCM.map f + Work.StemsB.IntRatCM.map g :=
    Functor.map_add (F := Work.StemsB.IntRatCM) (f := f) (g := g)
  simp only [dqMap, h, Work.Cohomology.dualComplexMap_add]

/-- The two comparison maps of a binary biproduct are mutually inverse as soon as the four
composites `P ≫ A`, `Q ≫ A`, `P ≫ B`, `Q ≫ B` are the identities and zeroes of the two
summands. -/
theorem biprod_desc_lift_eq_id {C : Type*} [Category C] [Preadditive C]
    {X Y Z : C} [HasBinaryBiproduct X Y]
    (A : Z ⟶ X) (B : Z ⟶ Y) (P : X ⟶ Z) (Q : Y ⟶ Z)
    (h₁ : P ≫ A = 𝟙 X) (h₂ : Q ≫ A = 0) (h₃ : P ≫ B = 0) (h₄ : Q ≫ B = 𝟙 Y) :
    biprod.desc P Q ≫ biprod.lift A B = 𝟙 (X ⊞ Y) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, Category.id_comp]
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, biprod.inl_fst]
      exact h₁
    · rw [← Category.assoc, biprod.inr_desc, biprod.inr_fst]
      exact h₂
  · rw [Category.assoc, biprod.lift_snd, Category.id_comp]
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, biprod.inl_snd]
      exact h₃
    · rw [← Category.assoc, biprod.inr_desc, biprod.inr_snd]
      exact h₄

theorem dqBiprodIsoSpec (C D : ChainComplex (ModuleCat Int) Nat) : ∃ (e : Work.Serre.DQ (CategoryTheory.Limits.biprod C D) ≅ CategoryTheory.Limits.biprod (Work.Serre.DQ C) (Work.Serre.DQ D)), e.hom = CategoryTheory.Limits.biprod.lift (Work.Serre.dqMap (CategoryTheory.Limits.biprod.inl : C ⟶ CategoryTheory.Limits.biprod C D)) (Work.Serre.dqMap (CategoryTheory.Limits.biprod.inr : D ⟶ CategoryTheory.Limits.biprod C D)) ∧ e.inv = CategoryTheory.Limits.biprod.desc (Work.Serre.dqMap (CategoryTheory.Limits.biprod.fst : CategoryTheory.Limits.biprod C D ⟶ C)) (Work.Serre.dqMap (CategoryTheory.Limits.biprod.snd : CategoryTheory.Limits.biprod C D ⟶ D)) := by
  refine ⟨{ hom := biprod.lift (dqMap (biprod.inl : C ⟶ biprod C D))
                          (dqMap (biprod.inr : D ⟶ biprod C D))
            inv := biprod.desc (dqMap (biprod.fst : biprod C D ⟶ C))
                          (dqMap (biprod.snd : biprod C D ⟶ D))
            hom_inv_id := ?_
            inv_hom_id := ?_ }, rfl, rfl⟩
  · rw [biprod.lift_desc, ← dqMap_comp (biprod.fst) (biprod.inl),
      ← dqMap_comp (biprod.snd) (biprod.inr),
      ← dqMap_add (f := biprod.fst ≫ biprod.inl) (g := biprod.snd ≫ biprod.inr),
      biprod.total, dqMap_id]
  · exact biprod_desc_lift_eq_id (A := dqMap (biprod.inl : C ⟶ biprod C D))
      (B := dqMap (biprod.inr : D ⟶ biprod C D))
      (P := dqMap (biprod.fst : biprod C D ⟶ C))
      (Q := dqMap (biprod.snd : biprod C D ⟶ D))
      (by rw [← dqMap_comp (biprod.inl) (biprod.fst), biprod.inl_fst, dqMap_id])
      (by rw [← dqMap_comp (biprod.inl) (biprod.snd), biprod.inl_snd, dqMap_zero])
      (by rw [← dqMap_comp (biprod.inr) (biprod.fst), biprod.inr_fst, dqMap_zero])
      (by rw [← dqMap_comp (biprod.inr) (biprod.snd), biprod.inr_snd, dqMap_id])

end Work.Serre
