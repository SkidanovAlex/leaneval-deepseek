import Mathlib
import Submission.Work.CFTLib.ContCohomology.Setup
import Submission.Work.CFTLib.ContCohomology.P1Iso

/-!
# `homShortComplex` computes continuous cohomology

Mathlib defines the continuous cohomology `continuousCohomology n X` of a topological
representation `X` of a topological group `Γ` as the homology of the complex of invariants of the
`coind₁`-resolution.  The file `P1Iso.lean` exhibits the classical description of that complex: its
`m`-th term is the module `homCochain X m` of invariant continuous functions on `Γ^{m+1}`, with
differential `homDiff X m`, and the termwise comparison is `evalIterEquiv X m`.

Here we globalise this to an isomorphism of short complexes: the concrete short complex
`homCochain X n → homCochain X (n+1) → homCochain X (n+2)` (`homShortComplex X n`) computes the
`(n+1)`-st continuous cohomology of `X`.

The comparison is carried out by

* forgetting the topology, i.e. applying `forget₂ (TopModuleCat k) (ModuleCat k)` — which is an
  exact functor, being both a left and a right adjoint, hence commutes with homology
  (`ShortComplex.mapHomologyIso`), and
* replacing `K.sc (n+1)` by the short complex `K.sc' n (n+1) (n+2)` on the nose
  (`HomologicalComplex.isoSc'`), since the `prev`/`next` of `ComplexShape.up ℕ` are not
  definitionally `n` and `n+2`.

## Main results

* `evalIterHomIso` — the termwise isomorphism in `ModuleCat k`.
* `homShortComplexIso` — the isomorphism of short complexes.
* `continuousCohomology_iso_homShortComplex` — the resulting linear equivalence on homology.
-/

noncomputable section

open TopRep CategoryTheory CategoryTheory.Limits

namespace Work.CFTLib.ContCohomology

variable {k Γ : Type} [CommRing k] [TopologicalSpace k] [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]

/-- The `m`-th term of the complex of invariants of the `coind₁`-resolution is the module of
invariant continuous functions on `Γ^{m+1}`, as an isomorphism in `ModuleCat k`. -/
noncomputable def evalIterHomIso (X : TopRep k Γ) (m : ℕ) :
    (forget₂ (TopModuleCat k) (ModuleCat k)).obj ((homogeneousCochains X).X m) ≅
      ModuleCat.of k ↥(homCochain X m) :=
  LinearEquiv.toModuleIso (evalIterEquiv X m)

/-- The underlying linear map of the image of a morphism of topological modules under the forgetful
functor to `ModuleCat k`. -/
lemma forget₂_map_hom {M N : TopModuleCat k} (f : M ⟶ N) :
    ((forget₂ (TopModuleCat k) (ModuleCat k)).map f).hom = (f.hom : ↥M →ₗ[k] ↥N) := rfl

/-- The first square of the isomorphism of short complexes: `evalIterEquiv` intertwines the
differentials. -/
lemma evalIterHomIso_comp_f (X : TopRep k Γ) (n : ℕ) :
    (evalIterHomIso X n).hom ≫ (homShortComplex X n).f =
      (((homogeneousCochains X).sc' n (n+1) (n+2)).map
        (forget₂ (TopModuleCat k) (ModuleCat k))).f ≫ (evalIterHomIso X (n+1)).hom := by
  show (evalIterHomIso X n).hom ≫ (homShortComplex X n).f =
    (((forget₂ (TopModuleCat k) (ModuleCat k)).map ((homogeneousCochains X).d n (n+1)) ≫
      (evalIterHomIso X (n+1)).hom) :
        (forget₂ (TopModuleCat k) (ModuleCat k)).obj ((homogeneousCochains X).X n) ⟶
          ModuleCat.of k ↥(homCochain X (n+1)))
  dsimp only [homShortComplex]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  dsimp only [evalIterHomIso, LinearEquiv.toModuleIso]
  rw [ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
  rw [forget₂_map_hom]
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_toLinearMap]
  rw [← evalIterEquiv_homDiff X n (show ↥((resolutionX X (n+1)).ρ.invariants) from x)]
  apply congrArg
  rw [homogeneousCochains.d_eq]
  rfl

/-- The second square of the isomorphism of short complexes. -/
lemma evalIterHomIso_comp_g (X : TopRep k Γ) (n : ℕ) :
    (evalIterHomIso X (n+1)).hom ≫ (homShortComplex X n).g =
      (((homogeneousCochains X).sc' n (n+1) (n+2)).map
        (forget₂ (TopModuleCat k) (ModuleCat k))).g ≫ (evalIterHomIso X (n+2)).hom := by
  show (evalIterHomIso X (n+1)).hom ≫ (homShortComplex X n).g =
    (((forget₂ (TopModuleCat k) (ModuleCat k)).map
        ((homogeneousCochains X).d (n+1) (n+2)) ≫
      (evalIterHomIso X (n+2)).hom) :
        (forget₂ (TopModuleCat k) (ModuleCat k)).obj ((homogeneousCochains X).X (n+1)) ⟶
          ModuleCat.of k ↥(homCochain X (n+2)))
  dsimp only [homShortComplex]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  dsimp only [evalIterHomIso, LinearEquiv.toModuleIso]
  rw [ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
  rw [forget₂_map_hom]
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_toLinearMap]
  rw [← evalIterEquiv_homDiff X (n+1) (show ↥((resolutionX X (n+2)).ρ.invariants) from x)]
  apply congrArg
  rw [homogeneousCochains.d_eq]
  rfl

/-- The concrete short complex `homCochain X n → homCochain X (n+1) → homCochain X (n+2)` is the
short complex of invariants of the `coind₁`-resolution, after forgetting the topology. -/
noncomputable def homShortComplexIso (X : TopRep k Γ) (n : ℕ) :
    (((homogeneousCochains X).sc' n (n+1) (n+2)).map
        (forget₂ (TopModuleCat k) (ModuleCat k))) ≅ homShortComplex X n :=
  ShortComplex.isoMk (evalIterHomIso X n) (evalIterHomIso X (n+1)) (evalIterHomIso X (n+2))
    (evalIterHomIso_comp_f X n) (evalIterHomIso_comp_g X n)

/-- `(homShortComplex X n).homology` is the `(n+1)`-st continuous cohomology of `X`: the
concrete short complex `homCochain X n → homCochain X (n+1) → homCochain X (n+2)` computes
`H^{n+1}`. -/
theorem continuousCohomology_iso_homShortComplex
    {k Γ : Type} [CommRing k] [TopologicalSpace k] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    (X : TopRep k Γ) (n : ℕ) :
    Nonempty (↥(continuousCohomology (n+1) X) ≃ₗ[k]
      ↥((Work.CFTLib.ContCohomology.homShortComplex X n).homology)) := by
  have h1 : (homogeneousCochains X).homology (n+1) ≅
      ((homogeneousCochains X).sc' n (n+1) (n+2)).homology :=
    ShortComplex.homologyMapIso
      ((homogeneousCochains X).isoSc' n (n+1) (n+2) (by simp) (by simp))
  have h2 : ((((homogeneousCochains X).sc' n (n+1) (n+2)).map
      (forget₂ (TopModuleCat k) (ModuleCat k))).homology) ≅
      (forget₂ (TopModuleCat k) (ModuleCat k)).obj
        (((homogeneousCochains X).sc' n (n+1) (n+2)).homology) :=
    ShortComplex.mapHomologyIso _ _
  have h3 : ((((homogeneousCochains X).sc' n (n+1) (n+2)).map
      (forget₂ (TopModuleCat k) (ModuleCat k))).homology) ≅ (homShortComplex X n).homology :=
    ShortComplex.homologyMapIso (homShortComplexIso X n)
  have hiso : (forget₂ (TopModuleCat k) (ModuleCat k)).obj
      ((homogeneousCochains X).homology (n+1)) ≅ (homShortComplex X n).homology :=
    (forget₂ (TopModuleCat k) (ModuleCat k)).mapIso h1 ≪≫ h2.symm ≪≫ h3
  have hEq : (forget₂ (TopModuleCat k) (ModuleCat k)).obj
      ((homogeneousCochains X).homology (n+1)) =
      (continuousCohomology (n+1) X).toModuleCat := rfl
  exact ⟨(hEq ▸ hiso).toLinearEquiv⟩

end Work.CFTLib.ContCohomology
