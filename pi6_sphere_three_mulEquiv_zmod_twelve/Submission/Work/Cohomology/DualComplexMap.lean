import Mathlib
import Submission.Work.Cohomology.DualComplex

/-!
# Functoriality of the dual (cochain) complex, and the dual of a homotopy

`Work.Cohomology.dualComplex R C` is the `R`-dual cochain complex of a chain complex `C` of
`R`-modules.  This file provides its contravariant functoriality:

* `dualComplexMapComp` — the `n`-th component of the dual of a chain map, `Hom(D_n,R) → Hom(C_n,R)`;
* `dualComplexMap` — **the dual of a chain map**, `f : C ⟶ D` giving `dualComplex D ⟶ dualComplex C`;
* `dualComplexMap_id`, `dualComplexMap_comp` — functoriality.

Everything here is stated for an arbitrary `CommRing R`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The transposed differential of the dual complex, as a composition with `d`. -/
@[simp]
theorem dualDiff_apply' (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (φ : (C.X n) →ₗ[R] R) :
    (dualDiff R C n).hom φ = φ.comp ((C.d (n + 1) n).hom) := rfl

/-- The `n`-th component of the dual of a chain map: the transpose
`Hom(D_n, R) ⟶ Hom(C_n, R)`. -/
def dualComplexMapComp (C D : ChainComplex (ModuleCat R) ℕ) (f : C ⟶ D) (n : ℕ) :
    dualObj R D n ⟶ dualObj R C n :=
  ModuleCat.ofHom ((f.f n).hom.dualMap)

/-- The `n`-th component of the dual of a chain map, as a composition. -/
@[simp]
theorem dualComplexMapComp_apply' (C D : ChainComplex (ModuleCat R) ℕ) (f : C ⟶ D) (n : ℕ)
    (φ : (D.X n) →ₗ[R] R) :
    (dualComplexMapComp R C D f n).hom φ = φ.comp ((f.f n).hom) := rfl

/-- Evaluation of the `n`-th component of the dual of a chain map. -/
theorem dualComplexMapComp_apply (C D : ChainComplex (ModuleCat R) ℕ) (f : C ⟶ D) (n : ℕ)
    (φ : (D.X n) →ₗ[R] R) (x : C.X n) :
    (dualComplexMapComp R C D f n).hom φ x = φ (((f.f n).hom) x) := by
  rw [dualComplexMapComp_apply', LinearMap.comp_apply]

/-- **The dual of a chain map**, as a cochain map `dualComplex D ⟶ dualComplex C`. -/
def dualComplexMap (C D : ChainComplex (ModuleCat R) ℕ) (f : C ⟶ D) :
    dualComplex R D ⟶ dualComplex R C :=
  CochainComplex.ofHom (fun n => dualComplexMapComp R C D f n) (fun n => by
    simp only [dualComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    apply LinearMap.ext
    intro φ
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [dualDiff_apply', dualComplexMapComp_apply', dualDiff_apply', dualComplexMapComp_apply',
      LinearMap.comp_assoc, LinearMap.comp_assoc]
    have hc := congrArg ModuleCat.Hom.hom (f.comm (n + 1) n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
    rw [hc])

/-- The components of `dualComplexMap` are `dualComplexMapComp`. -/
@[simp]
theorem dualComplexMap_f (C D : ChainComplex (ModuleCat R) ℕ) (f : C ⟶ D) (n : ℕ) :
    (dualComplexMap R C D f).f n = dualComplexMapComp R C D f n := rfl

/-- The `n`-th component of the dual of an identity chain map is the identity. -/
theorem dualComplexMapComp_id (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    dualComplexMapComp R C C (𝟙 C) n = 𝟙 (dualObj R C n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [dualComplexMapComp_apply', HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.comp_id,
    ModuleCat.hom_id, LinearMap.id_apply]

/-- The dual of the identity chain map is the identity. -/
theorem dualComplexMap_id (C : ChainComplex (ModuleCat R) ℕ) :
    dualComplexMap R C C (𝟙 C) = 𝟙 (dualComplex R C) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact dualComplexMapComp_id R C n

/-- The components of the dual of a composite. -/
theorem dualComplexMapComp_comp {C D E : ChainComplex (ModuleCat R) ℕ} (f : C ⟶ D) (g : D ⟶ E)
    (n : ℕ) :
    dualComplexMapComp R C E (CategoryTheory.CategoryStruct.comp f g) n
      = CategoryTheory.CategoryStruct.comp (dualComplexMapComp R D E g n)
        (dualComplexMapComp R C D f n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [dualComplexMapComp_apply', ModuleCat.hom_comp, LinearMap.comp_apply,
    dualComplexMapComp_apply', dualComplexMapComp_apply', HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_assoc]

/-- **Contravariant functoriality**: the dual of a composite is the composite of the duals. -/
theorem dualComplexMap_comp {C D E : ChainComplex (ModuleCat R) ℕ} (f : C ⟶ D) (g : D ⟶ E) :
    dualComplexMap R C E (CategoryTheory.CategoryStruct.comp f g)
      = CategoryTheory.CategoryStruct.comp (dualComplexMap R D E g)
        (dualComplexMap R C D f) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f]
  exact dualComplexMapComp_comp R f g n

end

end Work.Cohomology
