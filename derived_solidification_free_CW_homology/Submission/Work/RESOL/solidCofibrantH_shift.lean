/-
AREA RESOL — solid-cofibrant complexes are stable under shifts.

`SolidCofibrantH K` says that the localization `Qh : K(LightCondAb) ⥤ D(LightCondAb)`
induces bijections on the hom sets `Hom(K, hq (ιC.obj N))` for every complex `N` of solid
objects.  Both `K ↦ K⟦n⟧` and `N ↦ N⟦-n⟧` are autoequivalences, and `Qh` commutes with the
shifts, so the property only depends on the shift class of `K`: this is
`solidCofibrantH_shift`, the `shift` field of `CofibrantClosure` (`RESOL/Basic.lean`).

The proof has two ingredients, both proved below:
* `bijective_map_shift_iff`: for any functor `F` commuting with shifts, the bijectivity of
  `F` on `Hom(X⟦n⟧, Y)` is equivalent to the bijectivity of `F` on `Hom(X, Y⟦-n⟧)`
  (the shift equivalences on the source and the target are intertwined by the
  commutation isomorphisms of `F`);
* `bijective_Qh_map_of_iso_target`: bijectivity on `Hom(K, L)` only depends on `L` up to
  isomorphism (applied to `hq ((ιC.obj N)⟦-n⟧) ≅ hq (ιC.obj (N⟦-n⟧))`).
-/
import Mathlib
import Submission.Work.RESOL.Basic

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.RESOL

/-! ## Shifting a bijectivity statement along a functor commuting with shifts -/

/-- If `F : C ⥤ D` commutes with the shifts (by `ℤ`), then for any objects `X Y : C` and
`n : ℤ`, the map induced by `F` on `Hom(X⟦n⟧, Y)` is bijective if and only if the map induced
by `F` on `Hom(X, Y⟦-n⟧)` is bijective. -/
theorem bijective_map_shift_iff {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] (X Y : C) (n : ℤ) :
    Function.Bijective (fun f : X⟦n⟧ ⟶ Y => F.map f) ↔
      Function.Bijective (fun g : X ⟶ Y⟦-n⟧ => F.map g) := by
  have h : n + (-n) = 0 := add_neg_cancel n
  -- the bijection `Hom(X⟦n⟧, Y) ≃ Hom(X, Y⟦-n⟧)`, given by shifting by `-n` and using
  -- the structural isomorphism `X⟦n⟧⟦-n⟧ ≅ X`
  have hffC : Function.Bijective (fun f : X⟦n⟧ ⟶ Y => (shiftFunctor C (-n)).map f) :=
    ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩
  let φ : (X⟦n⟧ ⟶ Y) ≃ (X ⟶ Y⟦-n⟧) :=
    (Equiv.ofBijective _ hffC).trans
      (Iso.homCongr ((shiftFunctorCompIsoId C n (-n) h).app X) (Iso.refl (Y⟦-n⟧)))
  -- the analogous bijection on the side of `D`, using the commutation isomorphisms of `F`
  have hffD : Function.Bijective
      (fun g : (F.obj X)⟦n⟧ ⟶ F.obj Y => (shiftFunctor D (-n)).map g) :=
    ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩
  let ψ : (F.obj (X⟦n⟧) ⟶ F.obj Y) ≃ (F.obj X ⟶ F.obj (Y⟦-n⟧)) :=
    ((Iso.homCongr ((F.commShiftIso n).app X) (Iso.refl (F.obj Y))).trans
        (Equiv.ofBijective _ hffD)).trans
      (Iso.homCongr ((shiftFunctorCompIsoId D n (-n) h).app (F.obj X))
        (((F.commShiftIso (-n)).app Y).symm))
  -- the two bijections are intertwined by `F`
  have hG : ∀ f : X⟦n⟧ ⟶ Y, F.map ((shiftFunctor C (-n)).map f) =
      (F.commShiftIso (-n)).hom.app (X⟦n⟧) ≫ (shiftFunctor D (-n)).map (F.map f) ≫
        (F.commShiftIso (-n)).inv.app Y := by
    intro f
    calc F.map ((shiftFunctor C (-n)).map f)
        = (F.map ((shiftFunctor C (-n)).map f) ≫ (F.commShiftIso (-n)).hom.app Y) ≫
            (F.commShiftIso (-n)).inv.app Y := by simp
      _ = ((F.commShiftIso (-n)).hom.app (X⟦n⟧) ≫ (shiftFunctor D (-n)).map (F.map f)) ≫
            (F.commShiftIso (-n)).inv.app Y := by rw [Functor.commShiftIso_hom_naturality]
      _ = _ := by simp only [Category.assoc]
  have hkey : ∀ f : X⟦n⟧ ⟶ Y, ψ (F.map f) = F.map (φ f) := by
    intro f
    simp only [ψ, φ, Equiv.trans_apply, Equiv.ofBijective_apply, Iso.homCongr_apply,
      Iso.refl_hom, Category.comp_id, Category.assoc, Iso.symm_hom, Functor.map_comp,
      Iso.app_inv]
    rw [hG f, Functor.map_shiftFunctorCompIsoId_inv_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have key : (fun f : X⟦n⟧ ⟶ Y => ψ (F.map f)) = (fun f : X⟦n⟧ ⟶ Y => F.map (φ f)) := by
    funext f
    exact hkey f
  have h1 : Function.Bijective (fun f : X⟦n⟧ ⟶ Y => F.map f) ↔
      Function.Bijective (fun f : X⟦n⟧ ⟶ Y => ψ (F.map f)) :=
    (Function.Bijective.of_comp_iff'
      (f := fun h : F.obj (X⟦n⟧) ⟶ F.obj Y => ψ h) ψ.bijective
      (fun f : X⟦n⟧ ⟶ Y => F.map f)).symm
  have h2 : Function.Bijective (fun f : X⟦n⟧ ⟶ Y => ψ (F.map f)) ↔
      Function.Bijective (fun f : X⟦n⟧ ⟶ Y => F.map (φ f)) := by rw [key]
  have h3 : Function.Bijective (fun f : X⟦n⟧ ⟶ Y => F.map (φ f)) ↔
      Function.Bijective (fun g : X ⟶ Y⟦-n⟧ => F.map g) :=
    Equiv.bijective_comp φ (fun g : X ⟶ Y⟦-n⟧ => F.map g)
  exact h1.trans (h2.trans h3)

/-! ## Changing the target up to isomorphism -/

/-- The bijectivity of the localization `DerivedCategory.Qh` on `Hom(K, -)` only depends on the
target up to isomorphism. -/
theorem bijective_Qh_map_of_iso_target {K L L' : KCat} (e : L ≅ L')
    (h : Function.Bijective (fun f : K ⟶ L => DerivedCategory.Qh.map f)) :
    Function.Bijective (fun f : K ⟶ L' => DerivedCategory.Qh.map f) := by
  let Φ : (K ⟶ L) ≃ (K ⟶ L') := Iso.homCongr (Iso.refl K) e
  let Ψ : (DerivedCategory.Qh.obj K ⟶ DerivedCategory.Qh.obj L) ≃
      (DerivedCategory.Qh.obj K ⟶ DerivedCategory.Qh.obj L') :=
    Iso.homCongr (Iso.refl (DerivedCategory.Qh.obj K)) (DerivedCategory.Qh.mapIso e)
  have key : ∀ f : K ⟶ L, Ψ (DerivedCategory.Qh.map f) = DerivedCategory.Qh.map (Φ f) := by
    intro f
    simp only [Φ, Ψ, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, Functor.map_comp,
      Functor.mapIso_hom]
  have key2 : (fun f : K ⟶ L => Ψ (DerivedCategory.Qh.map f)) =
      (fun g : K ⟶ L' => DerivedCategory.Qh.map g) ∘ Φ.toFun := by
    funext f
    exact key f
  have h1 : Function.Bijective (fun f : K ⟶ L => Ψ (DerivedCategory.Qh.map f)) :=
    Function.Bijective.comp Ψ.bijective h
  rw [key2] at h1
  exact (Equiv.bijective_comp Φ (fun g : K ⟶ L' => DerivedCategory.Qh.map g)).mp h1

/-! ## The main statement -/

/-- Solid-cofibrant complexes are stable under shifts: this is the `shift` field of
`CofibrantClosure`. -/
theorem solidCofibrantH_shift (K : Work.RESOL.KCat) (n : ℤ) (hK : Work.RESOL.SolidCofibrantH K) :
    Work.RESOL.SolidCofibrantH ((CategoryTheory.shiftFunctor Work.RESOL.KCat n).obj K) := by
  intro N
  -- shift the source of the homs to the target, using that `Qh` commutes with shifts
  refine (bijective_map_shift_iff DerivedCategory.Qh K
    (Submission.Blueprint.hq (ιC.obj N)) n).mpr ?_
  -- `(hq (ιC.obj N))⟦-n⟧ = hq ((ιC.obj N)⟦-n⟧)`
  rw [HomotopyCategory.shift_quotient_obj]
  -- the degreewise inclusion commutes with shifts, so this is the hypothesis at `N⟦-n⟧`
  exact bijective_Qh_map_of_iso_target
    ((HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).mapIso
      ((ιC.commShiftIso (-n)).app N)) (hK (N⟦-n⟧))

end Work.RESOL
