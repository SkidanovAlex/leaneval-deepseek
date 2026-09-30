import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.uctDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The `Hom(-, G)` cochain complex of a chain complex, and coefficient changes

Towards the torsion universal coefficient theorem
`Hⁿ(Hom(C, ℤ)) ≅ Hom(H_{n-1}(C), ℚ/ℤ)` for a chain complex of free `ℤ`-modules whose homology
in degrees `n` and `n-1` is torsion.

This file provides the basic vocabulary:

* `homObj G C n = Hom_ℤ(Cₙ, G)`;
* `homDiff G C n`, `homComplex G C` — the cochain complex of `Hom(-, G)`;
* `homComplexMap φ C` — its functoriality in the coefficient group `G`;
* `homComplex_int_eq_dualComplex` — for `G = ℤ` this is the library's `dualComplex`;
* `homPre`, `homology_homComplex_iso` — `Hⁿ` as `ker δⁿ ⧸ im δⁿ⁻¹`;
* `intToRat`, `ratToQZ` — the coefficient maps `ℤ → ℚ` and `ℚ → ℚ/ℤ`;
* the injectivity of `ℚ` and `ℚ/ℤ` as `ℤ`-modules.

NOTE for downstream files: the two `local instance` lines below make the module structure on a
submodule (resp. a quotient by a submodule) of a `ℤ`-module the one induced from the ambient
module.  They are needed so that `↥B →ₗ[ℤ] ℤ` is elaborated with the same module structure
everywhere; please repeat them in files that use this vocabulary.  Also, the `•` on a module
of linear maps comes with two non-definitionally-equal instances; when a `map_smul'`
obligation has to be discharged by hand, the robust route is to build the map from an
`AddMonoidHom` with `AddMonoidHom.toIntLinearMap`.
-/

set_option backward.isDefEq.respectTransparency false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EFACTS

noncomputable section

/-- `Hom_ℤ(Cₙ, G)` as an object of `ModuleCat ℤ`. -/
abbrev homObj (G : Type) [AddCommGroup G] [Module ℤ G] (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    ModuleCat ℤ :=
  ModuleCat.of ℤ (↥(C.X n) →ₗ[ℤ] G)

/-- The transposed differential `f ↦ f ∘ d` of the `Hom(-, G)`-complex. -/
def homDiff (G : Type) [AddCommGroup G] [Module ℤ G] (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    homObj G C n ⟶ homObj G C (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun f => f.comp ((C.d (n + 1) n).hom)
      map_add' := fun f g => by ext x; simp [LinearMap.add_comp]
      map_smul' := fun a f => by ext x; rfl }

theorem homDiff_comp (G : Type) [AddCommGroup G] [Module ℤ G]
    (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    homDiff G C n ≫ homDiff G C (n + 1) = 0 := by
  have htotal : ((C.d (n + 1) n).hom).comp ((C.d ((n + 1) + 1) (n + 1)).hom) = 0 := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_zero]
    exact congrArg ModuleCat.Hom.hom
      (HomologicalComplex.d_comp_d C ((n + 1) + 1) (n + 1) n)
  have key : ∀ y : C.X ((n + 1) + 1),
      ((C.d (n + 1) n).hom) (((C.d ((n + 1) + 1) (n + 1)).hom) y) = 0 := by
    intro y
    have h := LinearMap.congr_fun htotal y
    simpa [LinearMap.comp_apply] using h
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, homDiff, ModuleCat.hom_ofHom]
  ext f x
  change f (((C.d (n + 1) n).hom) (((C.d ((n + 1) + 1) (n + 1)).hom) x)) = 0
  rw [key x]
  exact map_zero f

/-- **The `Hom(-, G)` cochain complex** of a chain complex of `ℤ`-modules. -/
def homComplex (G : Type) [AddCommGroup G] [Module ℤ G] (C : ChainComplex (ModuleCat ℤ) ℕ) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (homObj G C) (homDiff G C) (homDiff_comp G C)

@[simp]
theorem homComplex_X (G : Type) [AddCommGroup G] [Module ℤ G]
    (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (homComplex G C).X n = homObj G C n := rfl

@[simp]
theorem homComplex_d (G : Type) [AddCommGroup G] [Module ℤ G]
    (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (homComplex G C).d n (n + 1) = homDiff G C n :=
  CochainComplex.of_d (homObj G C) (homDiff G C) n

/-- For `G = ℤ` the `Hom(-, G)`-complex is the library's dual complex. -/
theorem homComplex_int_eq_dualComplex (C : ChainComplex (ModuleCat ℤ) ℕ) :
    homComplex ℤ C = Work.Cohomology.dualComplex ℤ C := rfl

/-- Postcomposition with a linear map of coefficient groups, as a morphism of `Hom(-, G)`
complexes.  (Built from an `AddMonoidHom` so that the `map_smul'` obligation is Mathlib's.) -/
def homComplexMap {G G' : Type} [AddCommGroup G] [Module ℤ G] [AddCommGroup G']
    [Module ℤ G'] (φ : G →ₗ[ℤ] G') (C : ChainComplex (ModuleCat ℤ) ℕ) :
    homComplex G C ⟶ homComplex G' C :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (AddMonoidHom.toIntLinearMap
      { toFun := fun f => φ.comp f
        map_zero' := by ext x; simp
        map_add' := fun f g => by ext x; simp }))
    (fun n => by
      apply ModuleCat.hom_ext
      simp only [homComplex_d, homDiff, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
      ext f x
      rfl)

@[simp]
theorem homComplexMap_f {G G' : Type} [AddCommGroup G] [Module ℤ G] [AddCommGroup G']
    [Module ℤ G'] (φ : G →ₗ[ℤ] G') (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (homComplexMap φ C).f n = ModuleCat.ofHom (AddMonoidHom.toIntLinearMap
      { toFun := fun f => φ.comp f
        map_zero' := by ext x; simp
        map_add' := fun f g => by ext x; simp }) := rfl

/-- The image of the transposed differential inside the cocycles of `homComplex G C`. -/
def homPre (G : Type) [AddCommGroup G] [Module ℤ G] (C : ChainComplex (ModuleCat ℤ) ℕ)
    (n : ℕ) : Submodule ℤ ↥(LinearMap.ker ((homComplex G C).d n (n + 1)).hom) :=
  LinearMap.range
    (((homComplex G C).d (n - 1) n).hom.codRestrict
      (LinearMap.ker ((homComplex G C).d n (n + 1)).hom) (fun x => by
        rw [LinearMap.mem_ker]
        have h := congrArg ModuleCat.Hom.hom
          (HomologicalComplex.d_comp_d (homComplex G C) (n - 1) n (n + 1))
        simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
        exact LinearMap.congr_fun h x))

/-- The `n`-th cohomology of `homComplex G C` is `ker δⁿ ⧸ im δⁿ⁻¹`. -/
theorem homology_homComplex_iso (G : Type) [AddCommGroup G] [Module ℤ G]
    (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    Nonempty ((homComplex G C).homology n ≅
      ModuleCat.of ℤ
        (↥(LinearMap.ker ((homComplex G C).d n (n + 1)).hom) ⧸ homPre G C n)) :=
  ⟨((homComplex G C).homologyIsoSc' (n - 1) n (n + 1)
        (Work.Cohomology.up_prev n) (Work.Cohomology.up_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso ((homComplex G C).sc' (n - 1) n (n + 1))⟩

/-- `ℤ → ℚ` as a `ℤ`-linear map. -/
def intToRat : ℤ →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap

/-- `ℚ → ℚ/ℤ` as a `ℤ`-linear map. -/
def ratToQZ : ℚ →ₗ[ℤ] AddCircle (1 : ℚ) :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap

/-- `ℚ` is injective as a `ℤ`-module. -/
theorem module_injective_rat : Module.Injective ℤ ℚ :=
  (Module.Baer.of_divisible ℚ).injective

/-- `ℚ/ℤ` is injective as a `ℤ`-module. -/
theorem module_injective_qz : Module.Injective ℤ (AddCircle (1 : ℚ)) :=
  (Module.Baer.of_divisible (AddCircle (1 : ℚ))).injective

end

end Work.Pi6.EFACTS
