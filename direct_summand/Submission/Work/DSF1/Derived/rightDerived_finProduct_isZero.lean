import Mathlib

namespace Work.DSF1.Derived

universe u v w x

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

/-- The chosen injective-resolution functor `C ⥤ HomotopyCategory C (ComplexShape.up ℕ)` is
additive.  On morphisms it is `f ↦ Q (InjectiveResolution.desc f …)`; the descent of `f + g` is
homotopic to the sum of the descents of `f` and `g`, because the latter is again a descent of
`f + g` (`InjectiveResolution.descHomotopy`). -/
instance injectiveResolutions_additive {C : Type u} [Category.{v} C] [Abelian C]
    [HasInjectiveResolutions C] : (injectiveResolutions C).Additive := by
  refine ⟨fun {X Y f g} => ?_⟩
  show (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc (f + g) (injectiveResolution Y) (injectiveResolution X)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X)) +
      (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X))
  rw [← Functor.map_add]
  refine HomotopyCategory.eq_of_homotopy _ _ (InjectiveResolution.descHomotopy (f + g) _ _ ?_ ?_) <;>
    simp [InjectiveResolution.desc_commutes]

/-- `F.rightDerivedToHomotopyCategory` is additive: it is the composite of the additive
injective-resolution functor with `F.mapHomotopyCategory`. -/
instance rightDerivedToHomotopyCategory_additive {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{x} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [HasInjectiveResolutions C] : (F.rightDerivedToHomotopyCategory).Additive := by
  dsimp [Functor.rightDerivedToHomotopyCategory]
  infer_instance

/-- The right derived functors `F.rightDerived k` of an additive functor are additive. -/
instance rightDerived_additive {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{x} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [HasInjectiveResolutions C] (k : ℕ) : (F.rightDerived k).Additive := by
  dsimp [Functor.rightDerived]
  infer_instance

/-- A finite product of zero objects is a zero object: the zero object, with the zero morphisms
as its structure maps, is a limit of any finite discrete diagram whose objects are zero
objects. -/
lemma isZero_pi_of_forall_isZero {D : Type w} [Category.{x} D] [Abelian D]
    {α : Type v} [Finite α] (Z : α → D) (h : ∀ i, IsZero (Z i)) : IsZero (∏ᶜ Z) := by
  have h0 : IsLimit (Fan.mk (0 : D) (fun i => (isZero_zero D).to_ (Z i)) : Fan Z) :=
    IsLimit.mk (fun s => (isZero_zero D).from_ s.pt)
      (fun s j => (h j.as).eq_of_tgt _ _)
      (fun s m hm => (isZero_zero D).eq_of_tgt _ _)
  exact IsZero.of_iso (isZero_zero D)
    (IsLimit.conePointUniqueUpToIso (productIsProduct Z) h0)

theorem rightDerived_finProduct_isZero {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C] [HasDerivedCategory C] {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D] [HasDerivedCategory D] (F : CategoryTheory.Functor C D) [CategoryTheory.Functor.Additive F] [CategoryTheory.EnoughInjectives C] {α : Type v} [Finite α] (R : α → C) (k : ℕ) (hk : 0 < k) (h : ∀ i, CategoryTheory.Limits.IsZero ((F.rightDerived k).obj (R i))) : CategoryTheory.Limits.IsZero ((F.rightDerived k).obj (∏ᶜ R)) := by
  haveI : PreservesFiniteProducts (F.rightDerived k) := by infer_instance
  refine IsZero.of_iso (isZero_pi_of_forall_isZero (fun i => (F.rightDerived k).obj (R i)) h) ?_
  exact PreservesProduct.iso (F.rightDerived k) R

end Work.DSF1.Derived
