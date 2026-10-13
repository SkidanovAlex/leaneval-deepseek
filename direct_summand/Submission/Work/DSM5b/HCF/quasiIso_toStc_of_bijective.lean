import Mathlib
import Submission.Work.DSM5b.HCF.Complex

set_option linter.style.haveILetI false

universe u

namespace Work.DSM5b.HCF

open CategoryTheory

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]

/-- The map induced by a componentwise bijective morphism of coefficient systems on the honest tuple
complexes is bijective: it is the product of the bijections `φ.φ (tupRng τ)`. -/
lemma htcMap_bijective {𝒜 ℬ : Work.DSM5b.CoeffSys R ι} (φ : Work.DSM5b.CoeffSys.Hom 𝒜 ℬ)
    (m : ℕ) (hφ : ∀ S : Finset ι, Function.Bijective (φ.φ S)) :
    Function.Bijective (Work.DSM5b.CoeffSys.Hom.htcMap φ m) := by
  constructor
  · intro z z' h
    funext τ
    exact (hφ (tupRng τ)).1 (by simpa using congr_fun h τ)
  · intro w
    refine ⟨fun τ => ((hφ (tupRng τ)).2 (w τ)).choose, ?_⟩
    funext τ
    simpa using ((hφ (tupRng τ)).2 (w τ)).choose_spec

/-- A componentwise bijective morphism of coefficient systems induces an isomorphism of honest tuple
complexes. -/
lemma isIso_htcHom {𝒜 ℬ : Work.DSM5b.CoeffSys R ι} (φ : Work.DSM5b.CoeffSys.Hom 𝒜 ℬ)
    (hφ : ∀ S : Finset ι, Function.Bijective (φ.φ S)) :
    IsIso (Work.DSM5b.htcHom φ) := by
  haveI : ∀ n : ℕ, IsIso ((Work.DSM5b.htcHom φ).f n) := by
    intro m
    rw [Work.DSM5b.htcHom_f]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (htcMap_bijective φ m hφ)
  exact HomologicalComplex.Hom.isIso_of_components (Work.DSM5b.htcHom φ)

variable [LinearOrder ι]

/-- The map induced by a componentwise bijective morphism of coefficient systems on the sorted
complexes is bijective: it is the product of the bijections `φ.φ (tupRng τ)`. -/
lemma stcMap_bijective {𝒜 ℬ : Work.DSM5b.CoeffSys R ι} (φ : Work.DSM5b.CoeffSys.Hom 𝒜 ℬ)
    (m : ℕ) (hφ : ∀ S : Finset ι, Function.Bijective (φ.φ S)) :
    Function.Bijective (Work.DSM5b.CoeffSys.Hom.stcMap φ m) := by
  constructor
  · intro z z' h
    funext τ
    exact (hφ (tupRng τ.1)).1 (by simpa using congr_fun h τ)
  · intro w
    refine ⟨fun τ => ((hφ (tupRng τ.1)).2 (w τ)).choose, ?_⟩
    funext τ
    simpa using ((hφ (tupRng τ.1)).2 (w τ)).choose_spec

/-- A componentwise bijective morphism of coefficient systems induces an isomorphism of sorted
complexes. -/
lemma isIso_stcHom {𝒜 ℬ : Work.DSM5b.CoeffSys R ι} (φ : Work.DSM5b.CoeffSys.Hom 𝒜 ℬ)
    (hφ : ∀ S : Finset ι, Function.Bijective (φ.φ S)) :
    IsIso (Work.DSM5b.stcHom φ) := by
  haveI : ∀ n : ℕ, IsIso ((Work.DSM5b.stcHom φ).f n) := by
    intro m
    rw [Work.DSM5b.stcHom_f]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (stcMap_bijective φ m hφ)
  exact HomologicalComplex.Hom.isIso_of_components (Work.DSM5b.stcHom φ)

/-- **Transfer of the comparison along a bijective morphism of coefficient systems.**  If a morphism
of coefficient systems `φ : 𝒜 ⟶ ℬ` (a family of linear maps commuting with the restriction maps) is
componentwise bijective, then the comparison map `toStc` is a quasi-isomorphism for `𝒜` as soon as
it is one for `ℬ`.

Route: the induced maps `htcHom φ : htcComplex 𝒜 ⟶ htcComplex ℬ` and
`stcHom φ : stcComplex 𝒜 ⟶ stcComplex ℬ` (`Work.DSM5b.htcHom`, `Work.DSM5b.stcHom`) are
isomorphisms of complexes, because their degree-`m` components are the products of the bijections
`φ.φ (tupRng τ)`; by `Work.DSM5b.toStcHom_natural` they fit into the square
`htcHom φ ≫ toStcHom ℬ = toStcHom 𝒜 ≫ stcHom φ`, so on homology the map induced by
`toStcHom 𝒜` is a composite of the map induced by `toStcHom ℬ` with isomorphisms, whence `IsIso`
(`IsIso.of_isIso_fac_left` / `IsIso.of_isIso_fac_right`, `HomologicalComplex.homologyMap_comp`);
conclude with `QuasiIso`/`quasiIsoAt_iff_isIso_homologyMap` (both root-level). -/
theorem quasiIso_toStc_of_bijective {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    [LinearOrder ι] {𝒜 ℬ : Work.DSM5b.CoeffSys R ι} (φ : Work.DSM5b.CoeffSys.Hom 𝒜 ℬ)
    (hφ : ∀ S : Finset ι, Function.Bijective (φ.φ S))
    (h : QuasiIso (Work.DSM5b.toStcHom ℬ)) : QuasiIso (Work.DSM5b.toStcHom 𝒜) := by
  haveI hiso_htc : IsIso (Work.DSM5b.htcHom φ) := isIso_htcHom φ hφ
  haveI hiso_stc : IsIso (Work.DSM5b.stcHom φ) := isIso_stcHom φ hφ
  haveI hqi_htc : QuasiIso (Work.DSM5b.htcHom φ) := inferInstance
  haveI hqi_stc : QuasiIso (Work.DSM5b.stcHom φ) := inferInstance
  haveI hqi_B : QuasiIso (Work.DSM5b.toStcHom ℬ) := h
  haveI hcomp : QuasiIso (Work.DSM5b.toStcHom 𝒜 ≫ Work.DSM5b.stcHom φ) := by
    rw [← Work.DSM5b.toStcHom_natural φ]
    exact quasiIso_comp (Work.DSM5b.htcHom φ) (Work.DSM5b.toStcHom ℬ)
  exact quasiIso_of_comp_right (Work.DSM5b.toStcHom 𝒜) (Work.DSM5b.stcHom φ)

end Work.DSM5b.HCF
