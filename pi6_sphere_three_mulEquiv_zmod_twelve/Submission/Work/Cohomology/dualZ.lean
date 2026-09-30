import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence

/-!
# The `ℤ`-dual of a `ℤ`-chain complex with values in an arbitrary ring `R`

`Work.Cohomology.dualComplex R C` (`Submission/Work/Cohomology/DualComplex.lean`) is the `R`-dual
of a chain complex **of `R`-modules**.  For the comparison of cohomology with coefficients in `R`
with homology with `ℤ`-coefficients one needs the variant where the *source* complex is a chain
complex of `ℤ`-modules while the *target* of `Hom` is an arbitrary commutative ring `R`:

* `dualZObj R C n` — the `R`-module `Hom_ℤ(C_n, R)`;
* `dualZDiff R C n` — the transposed differential `φ ↦ φ ∘ d`;
* `dualZ R C` — the resulting cochain complex of `R`-modules;
* `dualZMapComp`, `dualZMap` — contravariant functoriality;
* `dualZMap_id`, `dualZMap_comp` — functoriality.

Everything here is stated for an arbitrary `CommRing R`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The `n`-th `R`-dual module `Hom_ℤ(C_n, R)` of a `ℤ`-chain complex. -/
abbrev dualZObj (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) : ModuleCat R :=
  ModuleCat.of R ((C.X n) →ₗ[ℤ] R)

/-- The transposed differential `φ ↦ φ ∘ d` of a `ℤ`-chain complex. -/
def dualZDiff (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    dualZObj R C n ⟶ dualZObj R C (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun φ => φ.comp ((C.d (n + 1) n).hom)
      map_add' := fun φ ψ => by ext x; simp [LinearMap.comp_apply]
      map_smul' := fun a φ => by ext x; simp [LinearMap.comp_apply] }

/-- The transposed differential, as a composition with `d`. -/
@[simp]
theorem dualZDiff_apply' (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (φ : (C.X n) →ₗ[ℤ] R) :
    (dualZDiff R C n).hom φ = φ.comp ((C.d (n + 1) n).hom) := rfl

/-- Evaluation of the transposed differential. -/
theorem dualZDiff_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (φ : dualZObj R C n)
    (x : C.X (n + 1)) :
    (dualZDiff R C n).hom φ x = φ (((C.d (n + 1) n).hom) x) := by
  rw [dualZDiff_apply', LinearMap.comp_apply]

/-- The transposed differentials compose to zero. -/
theorem dualZDiff_comp (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    dualZDiff R C n ≫ dualZDiff R C (n + 1) = 0 := by
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
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, dualZDiff, ModuleCat.hom_ofHom]
  ext f x
  change f (((C.d (n + 1) n).hom) (((C.d ((n + 1) + 1) (n + 1)).hom) x)) = 0
  rw [key x]
  exact map_zero f

/-- **The `ℤ`-dual cochain complex with values in `R`** of a `ℤ`-chain complex. -/
def dualZ (C : ChainComplex (ModuleCat ℤ) ℕ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (dualZObj R C) (dualZDiff R C) (dualZDiff_comp R C)

@[simp]
theorem dualZ_X (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (dualZ R C).X n = dualZObj R C n := rfl

@[simp]
theorem dualZ_d (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (dualZ R C).d n (n + 1) = dualZDiff R C n :=
  CochainComplex.of_d (dualZObj R C) (dualZDiff R C) n

/-! ## Contravariant functoriality -/

/-- The `n`-th component of the `ℤ`-dual of a chain map: the transpose
`Hom_ℤ(D_n, R) ⟶ Hom_ℤ(C_n, R)`. -/
def dualZMapComp (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ) :
    dualZObj R D n ⟶ dualZObj R C n :=
  ModuleCat.ofHom
    { toFun := fun φ => φ.comp ((f.f n).hom)
      map_add' := fun φ ψ => by ext x; simp [LinearMap.comp_apply]
      map_smul' := fun a φ => by ext x; simp [LinearMap.comp_apply] }

/-- The `n`-th component of the dual of a chain map, as a composition. -/
@[simp]
theorem dualZMapComp_apply' (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ)
    (φ : (D.X n) →ₗ[ℤ] R) :
    (dualZMapComp R C D f n).hom φ = φ.comp ((f.f n).hom) := rfl

/-- Evaluation of the `n`-th component of the dual of a chain map. -/
theorem dualZMapComp_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ)
    (φ : dualZObj R D n) (x : C.X n) :
    (dualZMapComp R C D f n).hom φ x = φ (((f.f n).hom) x) := by
  rw [dualZMapComp_apply', LinearMap.comp_apply]

/-- **The `ℤ`-dual of a chain map**, as a cochain map `dualZ D ⟶ dualZ C`. -/
def dualZMap (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) :
    dualZ R D ⟶ dualZ R C :=
  CochainComplex.ofHom (fun n => dualZMapComp R C D f n) (fun n => by
    simp only [dualZ, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    apply LinearMap.ext
    intro φ
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [dualZDiff_apply', dualZMapComp_apply', dualZDiff_apply', dualZMapComp_apply',
      LinearMap.comp_assoc, LinearMap.comp_assoc]
    have hc := congrArg ModuleCat.Hom.hom (f.comm (n + 1) n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
    rw [hc])

@[simp]
theorem dualZMap_f (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ) :
    (dualZMap R C D f).f n = dualZMapComp R C D f n := rfl

/-- The `n`-th component of the dual of an identity chain map is the identity. -/
theorem dualZMapComp_id (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    dualZMapComp R C C (𝟙 C) n = 𝟙 (dualZObj R C n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [dualZMapComp_apply', HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.comp_id,
    ModuleCat.hom_id, LinearMap.id_apply]

/-- The `ℤ`-dual of the identity chain map is the identity. -/
theorem dualZMap_id (C : ChainComplex (ModuleCat ℤ) ℕ) :
    dualZMap R C C (𝟙 C) = 𝟙 (dualZ R C) := by
  ext n : 1
  rw [dualZMap_f, HomologicalComplex.id_f]
  exact dualZMapComp_id R C n

/-- The components of the dual of a composite are the composite of the components. -/
theorem dualZMapComp_comp (C D E : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (g : D ⟶ E)
    (n : ℕ) :
    dualZMapComp R C E (f ≫ g) n = dualZMapComp R D E g n ≫ dualZMapComp R C D f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, dualZMapComp_apply', dualZMapComp_apply',
    dualZMapComp_apply', HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_assoc]

/-- The `ℤ`-dual is contravariantly functorial. -/
theorem dualZMap_comp (C D E : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (g : D ⟶ E) :
    dualZMap R C E (f ≫ g) = dualZMap R D E g ≫ dualZMap R C D f := by
  ext n : 1
  rw [dualZMap_f, HomologicalComplex.comp_f, dualZMap_f, dualZMap_f]
  exact dualZMapComp_comp R C D E f g n

end

end Work.Cohomology

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology

variable (R : Type) [CommRing R]

/-- The components of the `ℤ`-dual of the zero chain map are zero. -/
theorem dualZMapComp_zero (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    dualZMapComp R C D (0 : C ⟶ D) n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [dualZMapComp_apply', HomologicalComplex.zero_f_apply, ModuleCat.hom_zero,
    LinearMap.comp_zero, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The `ℤ`-dual of the zero chain map is zero. -/
theorem dualZMap_zero (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    dualZMap R C D (0 : C ⟶ D) = 0 := by
  ext n : 1
  rw [dualZMap_f, HomologicalComplex.zero_f_apply]
  exact dualZMapComp_zero R C D n

/-- A short complex of `ℤ`-chain complexes whose first map is degreewise a split monomorphism (a
retraction of `S.f.f n` exists in every degree). -/
def IsDegreewiseSplit (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) : Prop :=
  ∀ n, ∃ r : S.X₂.X n ⟶ S.X₁.X n,
    CategoryTheory.CategoryStruct.comp (S.f.f n) r = CategoryTheory.CategoryStruct.id (S.X₁.X n)

/-- **The `ℤ`-dual (into `R`) short complex** of a short complex of `ℤ`-chain complexes:
`0 ⟶ dualZ R S.X₃ ⟶ dualZ R S.X₂ ⟶ dualZ R S.X₁ ⟶ 0`, the transposes of the maps of `S` in the
reverse order. -/
def dualZShort (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (dualZMap R S.X₂ S.X₃ S.g) (dualZMap R S.X₁ S.X₂ S.f) (by
    rw [← dualZMap_comp, S.zero, dualZMap_zero])

end

end Work.Cohomology
