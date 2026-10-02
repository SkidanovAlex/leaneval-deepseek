-- Islands subproject, 2026: this module is a copy of `Submission/Work/Cohomology/dualZ.lean`, and
-- Lean refuses a module whose transitive imports contain two declarations with the same name.  Every
-- declaration that this copy shares with the original is therefore renamed with the suffix `Compat`
-- (`dualZCompat`, `dualZCompat_X`, `dualZCompat_d`, `dualZObjCompat`, `dualZDiffCompat` and the
-- lemmas about it, `dualZMapCompat`, `dualZMapCompCompat`, `dualZShortCompat`,
-- `IsDegreewiseSplitCompat`).  Only `dualZ`/`dualZMap` had been renamed before, which is why the two
-- modules could not be imported into one file; they can now.  Statements unchanged.
import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `ℤ`-dual of a `ℤ`-chain complex with values in an arbitrary ring `R`

`Work.Cohomology.dualComplex R C` (`Submission/Work/Cohomology/DualComplex.lean`) is the `R`-dual
of a chain complex **of `R`-modules**.  For the comparison of cohomology with coefficients in `R`
with homology with `ℤ`-coefficients one needs the variant where the *source* complex is a chain
complex of `ℤ`-modules while the *target* of `Hom` is an arbitrary commutative ring `R`:

* `dualZObjCompat R C n` — the `R`-module `Hom_ℤ(C_n, R)`;
* `dualZDiffCompat R C n` — the transposed differential `φ ↦ φ ∘ d`;
* `dualZCompat R C` — the resulting cochain complex of `R`-modules;
* `dualZMapCompCompat`, `dualZMapCompat` — contravariant functoriality;
* `dualZMapCompat_id`, `dualZMapCompat_comp` — functoriality.

Everything here is stated for an arbitrary `CommRing R`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The `n`-th `R`-dual module `Hom_ℤ(C_n, R)` of a `ℤ`-chain complex. -/
abbrev dualZObjCompat (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) : ModuleCat R :=
  ModuleCat.of R ((C.X n) →ₗ[ℤ] R)

/-- The transposed differential `φ ↦ φ ∘ d` of a `ℤ`-chain complex. -/
def dualZDiffCompat (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    dualZObjCompat R C n ⟶ dualZObjCompat R C (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun φ => φ.comp ((C.d (n + 1) n).hom)
      map_add' := fun φ ψ => by ext x; simp [LinearMap.comp_apply]
      map_smul' := fun a φ => by ext x; simp [LinearMap.comp_apply] }

/-- The transposed differential, as a composition with `d`. -/
@[simp]
theorem dualZDiffCompat_apply' (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (φ : (C.X n) →ₗ[ℤ] R) :
    (dualZDiffCompat R C n).hom φ = φ.comp ((C.d (n + 1) n).hom) := rfl

/-- Evaluation of the transposed differential. -/
theorem dualZDiffCompat_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (φ : dualZObjCompat R C n)
    (x : C.X (n + 1)) :
    (dualZDiffCompat R C n).hom φ x = φ (((C.d (n + 1) n).hom) x) := by
  rw [dualZDiffCompat_apply', LinearMap.comp_apply]

/-- The transposed differentials compose to zero. -/
theorem dualZDiffCompat_comp (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    dualZDiffCompat R C n ≫ dualZDiffCompat R C (n + 1) = 0 := by
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
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, dualZDiffCompat, ModuleCat.hom_ofHom]
  ext f x
  change f (((C.d (n + 1) n).hom) (((C.d ((n + 1) + 1) (n + 1)).hom) x)) = 0
  rw [key x]
  exact map_zero f

/-- **The `ℤ`-dual cochain complex with values in `R`** of a `ℤ`-chain complex. -/
def dualZCompat (C : ChainComplex (ModuleCat ℤ) ℕ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (dualZObjCompat R C) (dualZDiffCompat R C) (dualZDiffCompat_comp R C)

@[simp]
theorem dualZCompat_X (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (dualZCompat R C).X n = dualZObjCompat R C n := rfl

@[simp]
theorem dualZCompat_d (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (dualZCompat R C).d n (n + 1) = dualZDiffCompat R C n :=
  CochainComplex.of_d (dualZObjCompat R C) (dualZDiffCompat R C) n

/-! ## Contravariant functoriality -/

/-- The `n`-th component of the `ℤ`-dual of a chain map: the transpose
`Hom_ℤ(D_n, R) ⟶ Hom_ℤ(C_n, R)`. -/
def dualZMapCompCompat (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ) :
    dualZObjCompat R D n ⟶ dualZObjCompat R C n :=
  ModuleCat.ofHom
    { toFun := fun φ => φ.comp ((f.f n).hom)
      map_add' := fun φ ψ => by ext x; simp [LinearMap.comp_apply]
      map_smul' := fun a φ => by ext x; simp [LinearMap.comp_apply] }

/-- The `n`-th component of the dual of a chain map, as a composition. -/
@[simp]
theorem dualZMapCompCompat_apply' (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ)
    (φ : (D.X n) →ₗ[ℤ] R) :
    (dualZMapCompCompat R C D f n).hom φ = φ.comp ((f.f n).hom) := rfl

/-- Evaluation of the `n`-th component of the dual of a chain map. -/
theorem dualZMapCompCompat_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ)
    (φ : dualZObjCompat R D n) (x : C.X n) :
    (dualZMapCompCompat R C D f n).hom φ x = φ (((f.f n).hom) x) := by
  rw [dualZMapCompCompat_apply', LinearMap.comp_apply]

/-- **The `ℤ`-dual of a chain map**, as a cochain map `dualZCompat D ⟶ dualZCompat C`. -/
def dualZMapCompat (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) :
    dualZCompat R D ⟶ dualZCompat R C :=
  CochainComplex.ofHom (fun n => dualZMapCompCompat R C D f n) (fun n => by
    simp only [dualZCompat, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    apply LinearMap.ext
    intro φ
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [dualZDiffCompat_apply', dualZMapCompCompat_apply', dualZDiffCompat_apply', dualZMapCompCompat_apply',
      LinearMap.comp_assoc, LinearMap.comp_assoc]
    have hc := congrArg ModuleCat.Hom.hom (f.comm (n + 1) n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
    rw [hc])

@[simp]
theorem dualZMapCompat_f (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ) :
    (dualZMapCompat R C D f).f n = dualZMapCompCompat R C D f n := rfl

/-- The `n`-th component of the dual of an identity chain map is the identity. -/
theorem dualZMapCompCompat_id (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    dualZMapCompCompat R C C (𝟙 C) n = 𝟙 (dualZObjCompat R C n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [dualZMapCompCompat_apply', HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.comp_id,
    ModuleCat.hom_id, LinearMap.id_apply]

/-- The `ℤ`-dual of the identity chain map is the identity. -/
theorem dualZMapCompat_id (C : ChainComplex (ModuleCat ℤ) ℕ) :
    dualZMapCompat R C C (𝟙 C) = 𝟙 (dualZCompat R C) := by
  ext n : 1
  rw [dualZMapCompat_f, HomologicalComplex.id_f]
  exact dualZMapCompCompat_id R C n

/-- The components of the dual of a composite are the composite of the components. -/
theorem dualZMapCompCompat_comp (C D E : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (g : D ⟶ E)
    (n : ℕ) :
    dualZMapCompCompat R C E (f ≫ g) n = dualZMapCompCompat R D E g n ≫ dualZMapCompCompat R C D f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, dualZMapCompCompat_apply', dualZMapCompCompat_apply',
    dualZMapCompCompat_apply', HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_assoc]

/-- The `ℤ`-dual is contravariantly functorial. -/
theorem dualZMapCompat_comp (C D E : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (g : D ⟶ E) :
    dualZMapCompat R C E (f ≫ g) = dualZMapCompat R D E g ≫ dualZMapCompat R C D f := by
  ext n : 1
  rw [dualZMapCompat_f, HomologicalComplex.comp_f, dualZMapCompat_f, dualZMapCompat_f]
  exact dualZMapCompCompat_comp R C D E f g n

end

end Work.Cohomology

namespace Work.Cohomology

noncomputable section

open CategoryTheory AlgebraicTopology

variable (R : Type) [CommRing R]

/-- The components of the `ℤ`-dual of the zero chain map are zero. -/
theorem dualZMapCompCompat_zero (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    dualZMapCompCompat R C D (0 : C ⟶ D) n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [dualZMapCompCompat_apply', HomologicalComplex.zero_f_apply, ModuleCat.hom_zero,
    LinearMap.comp_zero, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The `ℤ`-dual of the zero chain map is zero. -/
theorem dualZMapCompat_zero (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    dualZMapCompat R C D (0 : C ⟶ D) = 0 := by
  ext n : 1
  rw [dualZMapCompat_f, HomologicalComplex.zero_f_apply]
  exact dualZMapCompCompat_zero R C D n

/-- A short complex of `ℤ`-chain complexes whose first map is degreewise a split monomorphism (a
retraction of `S.f.f n` exists in every degree). -/
def IsDegreewiseSplitCompat (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) : Prop :=
  ∀ n, ∃ r : S.X₂.X n ⟶ S.X₁.X n,
    CategoryTheory.CategoryStruct.comp (S.f.f n) r = CategoryTheory.CategoryStruct.id (S.X₁.X n)

/-- **The `ℤ`-dual (into `R`) short complex** of a short complex of `ℤ`-chain complexes:
`0 ⟶ dualZCompat R S.X₃ ⟶ dualZCompat R S.X₂ ⟶ dualZCompat R S.X₁ ⟶ 0`, the transposes of the maps of `S` in the
reverse order. -/
def dualZShortCompat (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (dualZMapCompat R S.X₂ S.X₃ S.g) (dualZMapCompat R S.X₁ S.X₂ S.f) (by
    rw [← dualZMapCompat_comp, S.zero, dualZMapCompat_zero])

end

end Work.Cohomology
