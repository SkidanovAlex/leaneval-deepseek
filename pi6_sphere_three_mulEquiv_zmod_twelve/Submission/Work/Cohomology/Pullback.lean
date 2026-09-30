import Mathlib
import Submission.Work.Cohomology.Singular

/-!
# Functoriality of singular cohomology

A continuous map `f : X ⟶ Y` induces a chain map `C_*(X) ⟶ C_*(Y)` on singular chains, hence
(by transposition) a *cochain* map `C^*(Y) ⟶ C^*(X)`, hence a map
`Hⁿ(Y; R) ⟶ Hⁿ(X; R)` on singular cohomology.  This file provides that construction and its
functoriality (`id` and `comp`).

* `Work.Cohomology.cochainPullbackHom` — the `n`-th component;
* `Work.Cohomology.dualChainMap` — the induced cochain map `C^*(Y) ⟶ C^*(X)`;
* `Work.Cohomology.singularCohomologyMap` — the induced map `Hⁿ(Y;R) ⟶ Hⁿ(X;R)`;
* `Work.Cohomology.singularCohomologyMap_id`, `Work.Cohomology.singularCohomologyMap_comp`.

The remaining ingredient of contravariance (homotopy invariance: homotopic continuous maps induce
*equal* maps on cohomology) is delegated separately.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The chain map of singular chains induced by a continuous map. -/
abbrev chainMap (X Y : TopCat) (f : X ⟶ Y) :
    singularChains R X ⟶ singularChains R Y :=
  ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map f

/-- The `n`-th component of the cochain map induced by a continuous map: the transpose of the
`n`-th component of the chain map induced on singular chains. -/
def cochainPullbackHom (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    dualChains R Y n ⟶ dualChains R X n :=
  ModuleCat.ofHom ((chainMap R X Y f).f n).hom.dualMap

/-- The dual differential, evaluated. -/
@[simp]
theorem dualDifferential_apply (X : TopCat) (n : ℕ) (φ : dualChains R X n)
    (x : (singularChains R X).X (n + 1)) :
    (dualDifferential R X n).hom φ x = φ (((singularChains R X).d (n + 1) n).hom x) := by
  simp [dualDifferential, ModuleCat.hom_ofHom]

/-- The `n`-th component of the pullback, evaluated. -/
@[simp]
theorem cochainPullbackHom_apply (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (φ : dualChains R Y n) (x : (singularChains R X).X n) :
    (cochainPullbackHom R X Y f n).hom φ x = φ (((chainMap R X Y f).f n).hom x) := by
  simp only [cochainPullbackHom, ModuleCat.hom_ofHom, LinearMap.dualMap_apply]

/-- The cochain map `C^*(Y; R) ⟶ C^*(X; R)` induced by a continuous map `f : X ⟶ Y`. -/
def dualChainMap (X Y : TopCat) (f : X ⟶ Y) :
    singularCochainComplex R Y ⟶ singularCochainComplex R X :=
  CochainComplex.ofHom (fun n => cochainPullbackHom R X Y f n) (fun n => by
    simp only [singularCochainComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    have hc := congrArg ModuleCat.Hom.hom
      ((chainMap R X Y f).comm (n + 1) n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
    have hcx : ((singularChains R Y).d (n + 1) n).hom (((chainMap R X Y f).f (n + 1)).hom x)
        = ((chainMap R X Y f).f n).hom (((singularChains R X).d (n + 1) n).hom x) :=
      LinearMap.congr_fun hc x
    change φ (((chainMap R X Y f).f n).hom (((singularChains R X).d (n + 1) n).hom x))
      = φ (((singularChains R Y).d (n + 1) n).hom (((chainMap R X Y f).f (n + 1)).hom x))
    rw [hcx])

/-- The `n`-th component of the cochain map induced by an identity is the identity. -/
theorem cochainPullbackHom_id (X : TopCat) (n : ℕ) :
    cochainPullbackHom R X X (𝟙 X) n = 𝟙 (dualChains R X n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  rw [cochainPullbackHom_apply, ModuleCat.hom_id, LinearMap.id_apply]
  have h : ((chainMap R X X (𝟙 X)).f n).hom = LinearMap.id := by
    simp only [chainMap, CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.hom_id]
  rw [h, LinearMap.id_apply]

/-- The components of the cochain map induced by a composite. -/
theorem cochainPullbackHom_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    cochainPullbackHom R X Z (f ≫ g) n =
      cochainPullbackHom R Y Z g n ≫ cochainPullbackHom R X Y f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  simp only [cochainPullbackHom, chainMap, CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.dualMap_apply, LinearMap.comp_apply]

/-- The map induced by a continuous map on singular cohomology: contravariance. -/
def singularCohomologyMap (X Y : TopCat) (f : X ⟶ Y) (n : ℕ) :
    singularCohomology R n Y ⟶ singularCohomology R n X :=
  HomologicalComplex.homologyMap (dualChainMap R X Y f) n

/-- The cochain map induced by an identity is the identity. -/
theorem dualChainMap_id (X : TopCat) :
    dualChainMap R X X (𝟙 X) = 𝟙 (singularCochainComplex R X) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact cochainPullbackHom_id R X i

/-- The cochain map induced by a composite is the composite of the induced cochain maps
(contravariance). -/
theorem dualChainMap_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dualChainMap R X Z (f ≫ g) = dualChainMap R Y Z g ≫ dualChainMap R X Y f := by
  apply HomologicalComplex.hom_ext
  intro i
  exact cochainPullbackHom_comp R f g i

@[simp]
theorem singularCohomologyMap_id (X : TopCat) (n : ℕ) :
    singularCohomologyMap R X X (𝟙 X) n = 𝟙 (singularCohomology R n X) := by
  rw [singularCohomologyMap, dualChainMap_id, HomologicalComplex.homologyMap_id]
  simp only [singularCohomology]

theorem singularCohomologyMap_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    singularCohomologyMap R X Z (f ≫ g) n =
      singularCohomologyMap R Y Z g n ≫ singularCohomologyMap R X Y f n := by
  rw [singularCohomologyMap, singularCohomologyMap, singularCohomologyMap, dualChainMap_comp,
    HomologicalComplex.homologyMap_comp]

end

end Work.Cohomology
