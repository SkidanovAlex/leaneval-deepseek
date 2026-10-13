import Mathlib
import Submission.Work.DSG4a.tensorPi_extendScalars

namespace Work.DSEQ0

open CategoryTheory Limits

universe u

set_option linter.style.haveILetI false

/-- Extension of scalars along a ring homomorphism commutes with finite products, compatibly
with the projection maps.  This is the general-`φ` form of `Work.DSG4a.tensorPi_extendScalars`.

Since `ModuleCat.extendScalars φ` is additive and products over a finite index type are
biproducts, it preserves them; the compatibility with the projections is then the compatibility
of `Functor.mapBiproduct` with the biproduct projections. -/
lemma extendScalars_obj_pi_iso {A : Type u} [CommRing A] {S : Type u} [CommRing S]
    (φ : A →+* S) {ι : Type u} [Fintype ι] [DecidableEq ι] (M : ι → ModuleCat.{u} A) :
    ∃ e : (ModuleCat.extendScalars φ).obj (∏ᶜ M) ≅
        ∏ᶜ (fun i => (ModuleCat.extendScalars φ).obj (M i)),
      ∀ i, e.hom ≫ Pi.π (fun i => (ModuleCat.extendScalars φ).obj (M i)) i =
        (ModuleCat.extendScalars φ).map (Pi.π M i) := by
  haveI : (ModuleCat.extendScalars φ).Additive := Work.DSG4a.extendScalarsAdditivePi φ
  haveI : PreservesBiproduct M (ModuleCat.extendScalars φ) :=
    Work.DSG4a.preservesBiproduct_of_additive _ M
  refine ⟨(ModuleCat.extendScalars φ).mapIso (biproduct.isoProduct M).symm ≪≫
    Functor.mapBiproduct (ModuleCat.extendScalars φ) M ≪≫
    biproduct.isoProduct (fun i => (ModuleCat.extendScalars φ).obj (M i)), ?_⟩
  intro i
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [Iso.symm_hom, Functor.mapBiproduct_hom, biproduct.isoProduct_hom, biproduct.isoProduct_inv]
  simp only [Category.assoc]
  rw [Pi.lift_comp_π, biproduct.lift_π, ← Functor.map_comp, biproduct.lift_π]

theorem isIso_extendScalars_map_piMap
    {A : Type u} [CommRing A] {S : Type u} [CommRing S] (φ : A →+* S)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (M N : ι → ModuleCat.{u} A)
    (r : ∀ i, M i ⟶ N i)
    (h : ∀ i, CategoryTheory.IsIso ((ModuleCat.extendScalars φ).map (r i))) :
    CategoryTheory.IsIso ((ModuleCat.extendScalars φ).map (CategoryTheory.Limits.Pi.map r)) := by
  obtain ⟨eM, heM⟩ := extendScalars_obj_pi_iso φ M
  obtain ⟨eN, heN⟩ := extendScalars_obj_pi_iso φ N
  -- Naturality square relating `map (Pi.map r)` to `Pi.map (map r)`.
  have key : (ModuleCat.extendScalars φ).map (CategoryTheory.Limits.Pi.map r) ≫ eN.hom =
      eM.hom ≫ CategoryTheory.Limits.Pi.map
        (fun i => (ModuleCat.extendScalars φ).map (r i)) := by
    apply Pi.hom_ext
    intro i
    calc ((ModuleCat.extendScalars φ).map (CategoryTheory.Limits.Pi.map r) ≫ eN.hom) ≫
            Pi.π (fun i => (ModuleCat.extendScalars φ).obj (N i)) i
        = (ModuleCat.extendScalars φ).map (Pi.π M i) ≫
            (ModuleCat.extendScalars φ).map (r i) := by
          rw [Category.assoc, heN i, ← Functor.map_comp, CategoryTheory.Limits.Pi.map_π,
            Functor.map_comp]
      _ = (eM.hom ≫ CategoryTheory.Limits.Pi.map
              (fun i => (ModuleCat.extendScalars φ).map (r i))) ≫
            Pi.π (fun i => (ModuleCat.extendScalars φ).obj (N i)) i := by
          rw [Category.assoc, CategoryTheory.Limits.Pi.map_π, ← Category.assoc, heM i]
  have hsplit : (ModuleCat.extendScalars φ).map (CategoryTheory.Limits.Pi.map r) =
      eM.hom ≫ CategoryTheory.Limits.Pi.map
        (fun i => (ModuleCat.extendScalars φ).map (r i)) ≫ eN.inv := by
    calc (ModuleCat.extendScalars φ).map (CategoryTheory.Limits.Pi.map r)
        = ((ModuleCat.extendScalars φ).map (CategoryTheory.Limits.Pi.map r) ≫ eN.hom) ≫
            eN.inv := by
            rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (eM.hom ≫ CategoryTheory.Limits.Pi.map
              (fun i => (ModuleCat.extendScalars φ).map (r i))) ≫ eN.inv := by
            rw [key]
      _ = eM.hom ≫ CategoryTheory.Limits.Pi.map
            (fun i => (ModuleCat.extendScalars φ).map (r i)) ≫ eN.inv :=
            Category.assoc _ _ _
  rw [hsplit]
  infer_instance

end Work.DSEQ0
