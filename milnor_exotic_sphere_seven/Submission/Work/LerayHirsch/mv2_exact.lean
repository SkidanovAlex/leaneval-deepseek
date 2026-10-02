import Mathlib
import Submission.Work.LerayHirsch.LhGlueDefs
import Submission.Work.LerayHirsch.mv2_components
import Submission.Work.Thom.thomClass_of_cover
import Submission.Work.Thom.Relocate.HonestFMV

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.LerayHirsch

open CategoryTheory CategoryTheory.Limits
open Work.Thom

noncomputable section

/-- The underlying linear map of a composite of morphisms, right-associated. -/
lemma hom_comp_comp {A B C D : ModuleCat ℤ} (e : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D) :
    ModuleCat.Hom.hom (e ≫ f ≫ g)
      = ModuleCat.Hom.hom g ∘ₗ ModuleCat.Hom.hom f ∘ₗ ModuleCat.Hom.hom e := by
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]

lemma inj_hom_of_mono {A B : ModuleCat ℤ} (f : A ⟶ B) [Mono f] :
    Function.Injective (ModuleCat.Hom.hom f) :=
  (ModuleCat.mono_iff_injective f).mp inferInstance

lemma surj_hom_of_epi {A B : ModuleCat ℤ} (f : A ⟶ B) [Epi f] :
    Function.Surjective (ModuleCat.Hom.hom f) :=
  (ModuleCat.epi_iff_surjective f).mp inferInstance

/-- The range of `e.inv ≫ f ≫ e'.hom` is the image under `e'.hom` of the range of `f`. -/
lemma range_comp_iso_comp_iso {A B A' B' : ModuleCat ℤ} (e : A ≅ A') (e' : B ≅ B')
    (f : A ⟶ B) :
    (e.inv ≫ f ≫ e'.hom).hom.range
      = Submodule.map (ModuleCat.Hom.hom e'.hom) (ModuleCat.Hom.hom f).range := by
  rw [hom_comp_comp, LinearMap.range_comp, LinearMap.range_comp]
  have h : (ModuleCat.Hom.hom e.inv).range = ⊤ :=
    LinearMap.range_eq_top.mpr (surj_hom_of_epi e.inv)
  rw [h, Submodule.map_top]

/-- The kernel of `e'.inv ≫ g ≫ e''.hom` is the image under `e'.hom` of the kernel of `g`. -/
lemma ker_comp_iso_comp_iso {B C B' D : ModuleCat ℤ} (e' : B ≅ B') (e'' : C ≅ D)
    (g : B ⟶ C) :
    (e'.inv ≫ g ≫ e''.hom).hom.ker
      = Submodule.map (ModuleCat.Hom.hom e'.hom) (ModuleCat.Hom.hom g).ker := by
  have hinj : Function.Injective (ModuleCat.Hom.hom e''.hom) := inj_hom_of_mono e''.hom
  have hcomp : ModuleCat.Hom.hom e'.hom ∘ₗ ModuleCat.Hom.hom e'.inv = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom (Iso.inv_hom_id e')
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact h
  have hcomp' : ModuleCat.Hom.hom e'.inv ∘ₗ ModuleCat.Hom.hom e'.hom = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom (Iso.hom_inv_id e')
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact h
  have hmap (x : ↑B') : ModuleCat.Hom.hom e'.inv x = ModuleCat.Hom.hom e'.inv x := rfl
  rw [hom_comp_comp]
  ext x
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨ModuleCat.Hom.hom e'.inv x, ?_, ?_⟩
    · show ModuleCat.Hom.hom g (ModuleCat.Hom.hom e'.inv x) = 0
      apply hinj
      simpa using hx
    · show ModuleCat.Hom.hom e'.hom (ModuleCat.Hom.hom e'.inv x) = x
      simpa using congrArg (fun (l : ↑B' →ₗ[ℤ] ↑B') => l x) hcomp
  · rintro ⟨y, hy, rfl⟩
    show ModuleCat.Hom.hom e''.hom
      (ModuleCat.Hom.hom g (ModuleCat.Hom.hom e'.inv (ModuleCat.Hom.hom e'.hom y))) = 0
    have h1 : ModuleCat.Hom.hom e'.inv (ModuleCat.Hom.hom e'.hom y) = y :=
      congrArg (fun (l : ↑B →ₗ[ℤ] ↑B) => l y) hcomp'
    rw [h1, hy]
    simp

/-- Injectivity of `e.inv ≫ f ≫ e'.hom` follows from injectivity of `f`. -/
lemma injective_comp_iso_comp_iso {A B A' B' : ModuleCat ℤ} (e : A ≅ A') (e' : B ≅ B')
    (f : A ⟶ B) (hf : Function.Injective (ModuleCat.Hom.hom f)) :
    Function.Injective (e.inv ≫ f ≫ e'.hom).hom := by
  rw [hom_comp_comp]
  intro x y hxy
  simp only [LinearMap.comp_apply] at hxy
  have h1 : ModuleCat.Hom.hom f (ModuleCat.Hom.hom e.inv x)
      = ModuleCat.Hom.hom f (ModuleCat.Hom.hom e.inv y) :=
    inj_hom_of_mono e'.hom hxy
  have h2 := hf h1
  have h3 : ModuleCat.Hom.hom e.hom ∘ₗ ModuleCat.Hom.hom e.inv = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom (Iso.inv_hom_id e)
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact h
  have h4 : ModuleCat.Hom.hom e.hom (ModuleCat.Hom.hom e.inv x) = x :=
    congrArg (fun (l : ↑A' →ₗ[ℤ] ↑A') => l x) h3
  have h5 : ModuleCat.Hom.hom e.hom (ModuleCat.Hom.hom e.inv y) = y :=
    congrArg (fun (l : ↑A' →ₗ[ℤ] ↑A') => l y) h3
  rw [← h4, ← h5]
  exact congrArg (ModuleCat.Hom.hom e.hom) h2

/-! ## The two-set Mayer–Vietoris sequence of the chapter's cohomology -/

theorem mv2_exact {X : Type} [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    (∀ k : ℕ, (mv2F U V k).hom.range = (mv2G U V k).hom.ker) ∧
    (∀ k : ℕ, (mv2G U V k).hom.range = (mv2δ U V hU hV hcov k).hom.ker) ∧
    (∀ k : ℕ, (mv2δ U V hU hV hcov k).hom.range = (mv2F U V (k + 1)).hom.ker) ∧
    Function.Injective (mv2F U V 0).hom := by
  have h2 : ∀ k : ℕ,
      (Work.Cohomology.honestF (TopCat.of X) (∅ : Set X) U V k).hom.range
        = (Work.Cohomology.honestG (TopCat.of X) (∅ : Set X) U V k).hom.ker := fun k =>
    ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.honest_exact₂ (TopCat.of X) (∅ : Set X) U V hU hV hcov k)
  have h3 : ∀ k : ℕ,
      (Work.Cohomology.honestG (TopCat.of X) (∅ : Set X) U V k).hom.range
        = (Work.Cohomology.honestDelta (TopCat.of X) (∅ : Set X) U V hU hV hcov k).hom.ker := fun k =>
    ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.honest_exact₃ (TopCat.of X) (∅ : Set X) U V hU hV hcov k)
  have h1 : ∀ k : ℕ,
      (Work.Cohomology.honestDelta (TopCat.of X) (∅ : Set X) U V hU hV hcov k).hom.range
        = (Work.Cohomology.honestF (TopCat.of X) (∅ : Set X) U V (k + 1)).hom.ker := fun k =>
    ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.honest_exact₁ (TopCat.of X) (∅ : Set X) U V hU hV hcov k)
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, ?_⟩
  · rw [mv2F, mv2G, range_comp_iso_comp_iso, ker_comp_iso_comp_iso, h2 k]
  · rw [mv2G, mv2δ, range_comp_iso_comp_iso, ker_comp_iso_comp_iso, h3 k]
  · rw [mv2δ, mv2F, range_comp_iso_comp_iso, ker_comp_iso_comp_iso, h1 k]
  · exact injective_comp_iso_comp_iso (pdCohIso X 0)
      (biprod.mapIso (pdCohIso ↥U 0) (pdCohIso ↥V 0))
      (Work.Cohomology.honestF (TopCat.of X) (∅ : Set X) U V 0)
      (Work.Thom.honestF_injective_zero (TopCat.of X) (∅ : Set X) U V hU hV hcov)

end

end Work.LerayHirsch
