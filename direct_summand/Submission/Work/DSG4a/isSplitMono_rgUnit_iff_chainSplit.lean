import Mathlib
import Submission.Work.DSG4a.F1Interface
import Submission.Work.DSG4a.Criterion
import Submission.Work.DSG4a.isSplitMono_Q_map_iff_chainSplit

/-!
# DSG4a: `IsSplitMono (rgUnit A X f) ↔ ChainSplit P cc`

This is the bridge lemma announced in `Submission/Work/DSG4a/F1Interface.lean`: for a
K-projective model `P` of `RΓ(X, 𝒪_X)` together with a coaugmentation `cc : A[0] ⟶ P` and an
isomorphism `e : ι(RΓ(X, 𝒪_X)) ≅ Q(P)` compatible with the unit (`Criterion.F1UnitCompatible`),
the challenge unit `rgUnit A X f` is a split monomorphism in `D(A)` if and only if the
coaugmentation splits at the chain level (`Criterion.ChainSplit P cc`).

The compatibility hypothesis reads

`ι.map (rgUnit A X f) ≫ e.hom = a ≫ (b ≫ Q.map cc)`

where `a = (Plus.singleFunctorιIso C 0).hom.app A` and
`b = (singleFunctorIsoCompQ C 0).hom.app A` are components of isomorphisms of functors.  Hence the
proof is a sequence of transports of the property `IsSplitMono`:

* `Plus.ι` is fully faithful, so `IsSplitMono u ↔ IsSplitMono (Plus.ι.map u)`;
* `IsSplitMono` is unchanged by postcomposition with an isomorphism;
* `IsSplitMono` is unchanged by precomposition with an isomorphism;
* `isSplitMono_Q_map_iff_chainSplit` (the main theorem of
  `Submission/Work/DSG4a/isSplitMono_Q_map_iff_chainSplit.lean`) identifies
  `IsSplitMono (Q.map cc)` with `ChainSplit P cc`.
-/

set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.DSG4a

universe u v₁ v₂ v₃ v₄

section Generalities

/-- `IsSplitMono` is invariant under postcomposition with an isomorphism. -/
theorem rgUnit_isSplitMono_comp_iso {C : Type v₁} [Category.{v₂} C] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsIso g] : IsSplitMono (f ≫ g) ↔ IsSplitMono f := by
  constructor
  · intro h
    -- `f = (f ≫ g) ≫ g⁻¹`, and `IsSplitMono` is stable under composition
    have h2 : IsSplitMono ((f ≫ g) ≫ inv g) := by
      haveI := h
      exact inferInstance
    rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h2
  · intro h
    haveI := h
    exact inferInstance

/-- `IsSplitMono` is invariant under precomposition with an isomorphism. -/
theorem rgUnit_isSplitMono_iso_comp {C : Type v₁} [Category.{v₂} C] {X Y Z : C} (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Z) : IsSplitMono (f ≫ g) ↔ IsSplitMono g := by
  constructor
  · intro h
    -- `g = f⁻¹ ≫ (f ≫ g)`
    have h2 : IsSplitMono (inv f ≫ (f ≫ g)) := by
      haveI := h
      exact inferInstance
    rwa [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at h2
  · intro h
    haveI := h
    exact inferInstance

/-- A fully faithful functor neither creates nor destroys split monomorphisms. -/
theorem rgUnit_isSplitMono_map_iff_of_full_faithful {C : Type v₁} [Category.{v₂} C]
    {D : Type v₃} [Category.{v₄} D] (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C} (f : X ⟶ Y) :
    IsSplitMono (F.map f) ↔ IsSplitMono f := by
  constructor
  · rintro ⟨⟨r, hr⟩⟩
    obtain ⟨r', rfl⟩ := F.map_surjective r
    exact IsSplitMono.mk' ⟨r', F.map_injective (by rw [F.map_comp, hr, F.map_id])⟩
  · rintro ⟨⟨r, hr⟩⟩
    exact IsSplitMono.mk' ⟨F.map r, by rw [← F.map_comp, hr, F.map_id]⟩

end Generalities

section UnitComparison

/-- The comparison morphism `unitComparison` of the `F1` interface is an isomorphism followed by
`Q.map cc`; hence `IsSplitMono` of it is equivalent to `IsSplitMono (Q.map cc)`. -/
theorem rgUnit_isSplitMono_unitComparison_iff (A : Type u) [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P) :
    IsSplitMono (Criterion.unitComparison A P cc) ↔
      IsSplitMono (DerivedCategory.Q.map cc) := by
  rw [show Criterion.unitComparison A P cc =
      (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{u} A) 0).hom.app (ModuleCat.of A A) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).hom.app (ModuleCat.of A A) ≫
          DerivedCategory.Q.map cc) from rfl]
  rw [rgUnit_isSplitMono_iso_comp _ _, rgUnit_isSplitMono_iso_comp _ _]

end UnitComparison

theorem isSplitMono_rgUnit_iff_chainSplit {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [CategoryTheory.EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [CochainComplex.IsKProjective P]
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P)
    (e : CategoryTheory.Iso (DerivedCategory.Plus.ι.obj (DSMap.RG A X f)) (DerivedCategory.Q.obj P))
    (he : Work.DSG4a.Criterion.F1UnitCompatible P cc e) :
    CategoryTheory.IsSplitMono (DSMap.rgUnit A X f) ↔
      Work.DSG4a.Criterion.ChainSplit P cc := by
  have he' : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
      Criterion.unitComparison A P cc := he
  rw [← rgUnit_isSplitMono_map_iff_of_full_faithful (DerivedCategory.Plus.ι (C := ModuleCat.{u} A))
      (DSMap.rgUnit A X f),
    ← rgUnit_isSplitMono_comp_iso (DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f)) e.hom, he',
    rgUnit_isSplitMono_unitComparison_iff A P cc]
  exact isSplitMono_Q_map_iff_chainSplit P cc

end Work.DSG4a
