import Mathlib
import Submission.Work.TangentClasses.Cohomology
import Submission.Work.Cohomology.homotopyInvariance
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.RelMVLes
import Submission.Work.Cohomology.exists_relComplexMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The cohomology model of the Thom chapter

This module fixes the notation used throughout `Submission/Work/Thom/`: singular cohomology with
coefficients in an arbitrary commutative ring `R`, both absolute (`Coh R n B`) and relative
(`RelCoh R n B A`), together with the pullback `CohMap f R n`, the forgetful map
`relToAbs A R n : H^n(B,A;R) → H^n(B;R)`, and the exterior (mixed) cup product
`mixedCupC : H^m(B;R) → H^n(B,A;R) → H^{m+n}(B,A;R)` of an absolute with a relative class.

The point of working with a general coefficient ring `R` (and not only `ℤ`) is that the *same*
constructions give

* the **Euler class** `e(E) ∈ H^n(B;ℤ)` of an oriented rank-`n` real bundle (coefficients `ℤ`), and
* the **top Stiefel–Whitney class** `w_n(E) ∈ H^n(B;ℤ/2)` of an arbitrary rank-`n` bundle
  (coefficients `ℤ/2`),

from one Thom-class construction; see `Submission/Work/Thom/ThomClass.lean`.

The conventions are those of `Submission/Work/TangentClasses/Cohomology.lean`
(`Work.TangentClasses.H`, `Work.TangentClasses.HMap`) with the coefficient ring made explicit;
`Coh ℤ n B` is *definitionally* `Work.TangentClasses.H n B`.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- `H^n(B;R)`: singular cohomology of a topological space with coefficients in `R`, in the
workspace's cochain model.  (The workspace's cohomology is built for spaces in `Type 0`; all the
spaces of this chapter — total spaces of tangent bundles of manifolds modelled on
`EuclideanSpace ℝ (Fin n)`, disc and sphere bundles — are in `Type 0`.) -/
abbrev Coh (R : Type) [CommRing R] (n : ℕ) (B : Type) [TopologicalSpace B] : ModuleCat R :=
  Work.Cohomology.singularCohomology R n (TopCat.of B)

/-- The pullback `f^* : H^n(B₂;R) ⟶ H^n(B₁;R)` along a continuous map `f : C(B₁, B₂)`. -/
abbrev CohMap {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    (f : C(B₁, B₂)) (R : Type) [CommRing R] (n : ℕ) : Coh R n B₂ ⟶ Coh R n B₁ :=
  Work.Cohomology.singularCohomologyMap R (TopCat.of B₁) (TopCat.of B₂) (TopCat.ofHom f) n

/-- `H^n(B,A;R)`: relative singular cohomology of the pair `(B,A)`, i.e. the cohomology of the
cochain complex of cochains on `B` vanishing on singular simplices lying in `A`. -/
abbrev RelCoh (R : Type) [CommRing R] (n : ℕ) (B : Type) [TopologicalSpace B] (A : Set B) :
    ModuleCat R :=
  Work.Cohomology.relCohomology R (TopCat.of B) A n

/-- The **forgetful map** `H^n(B,A;R) → H^n(B;R)`: a class relative to `A` is in particular a
class on `B`. -/
abbrev relToAbs (R : Type) [CommRing R] {B : Type} [TopologicalSpace B] (A : Set B) (n : ℕ) :
    RelCoh R n B A ⟶ Coh R n B :=
  HomologicalComplex.homologyMap (Work.Cohomology.relIncl R (TopCat.of B) A) n

/-- The **exterior cup product** `H^m(B;R) → H^n(B,A;R) → H^{m+n}(B,A;R)`: the module structure of
the relative cohomology over the absolute cohomology. -/
abbrev mixedCupC (R : Type) [CommRing R] {B : Type} [TopologicalSpace B] (A : Set B) (m n : ℕ) :
    Coh R m B →ₗ[R] RelCoh R n B A →ₗ[R] RelCoh R (m + n) B A :=
  (Classical.choose (Work.Cohomology.mixedRelCupH R (TopCat.of B) A)) m n

/-- The **relative cup product** of two relative classes. -/
abbrev relCupC (R : Type) [CommRing R] {B : Type} [TopologicalSpace B] (A : Set B) (m n : ℕ) :
    RelCoh R m B A →ₗ[R] RelCoh R n B A →ₗ[R] RelCoh R (m + n) B A :=
  Work.Cohomology.relCupH' R (TopCat.of B) A m n

/-! ## Pullback of relative cohomology along a map of pairs -/

/-- The **pullback of relative cohomology along a map of pairs** `f : (X,A) → (Y,B)`: the induced
map `H^n(Y,B;R) ⟶ H^n(X,A;R)`, for a continuous map `f : C(X,Y)` with `f '' A ⊆ B`.  It is the map
on cohomology induced by `Work.Cohomology.relComplexMap`. -/
abbrev relCohMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (R : Type) [CommRing R] (n : ℕ) :
    RelCoh R n Y B ⟶ RelCoh R n X A :=
  HomologicalComplex.homologyMap
    (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B
      (TopCat.ofHom f) hf) n

/-- **The pullback of a relative class forgets to the pullback of its absolute class**: the two ways
round the square `H^n(Y,B) → H^n(X,A) → H^n(X)` and `H^n(Y,B) → H^n(Y) → H^n(X)` agree. -/
theorem relCohMap_relToAbs {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (R : Type) [CommRing R] (n : ℕ) :
    relCohMap f A B hf R n ≫ relToAbs R A n = relToAbs R B n ≫ CohMap f R n := by
  have hcomp : Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B
      (TopCat.ofHom f) hf ≫ Work.Cohomology.relIncl R (TopCat.of X) A =
      Work.Cohomology.relIncl R (TopCat.of Y) B ≫
        Work.Cohomology.dualChainMap R (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) := by
    apply HomologicalComplex.hom_ext
    intro k
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Work.Cohomology.relComplexMap_f,
      Work.Cohomology.relIncl_f, Work.Cohomology.relIncl_f]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    exact Work.Cohomology.relMapLM_coe (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B
      (TopCat.ofHom f) hf k x
  show HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
      (X₂ := TopCat.of Y) R A B (TopCat.ofHom f) hf) n ≫
      HomologicalComplex.homologyMap (Work.Cohomology.relIncl R (TopCat.of X) A) n =
    HomologicalComplex.homologyMap (Work.Cohomology.relIncl R (TopCat.of Y) B) n ≫
      HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap R (TopCat.of X) (TopCat.of Y)
        (TopCat.ofHom f)) n
  rw [← HomologicalComplex.homologyMap_comp, hcomp, HomologicalComplex.homologyMap_comp]

@[simp] theorem CohMap_id {B : Type} [TopologicalSpace B] (R : Type) [CommRing R] (n : ℕ) :
    CohMap (ContinuousMap.id B) R n = 𝟙 (Coh R n B) := by
  rw [CohMap, TopCat.ofHom_id, Work.Cohomology.singularCohomologyMap_id]

theorem CohMap_comp {B₁ B₂ B₃ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    [TopologicalSpace B₃] (f : C(B₁, B₂)) (g : C(B₂, B₃)) (R : Type) [CommRing R] (n : ℕ) :
    CohMap (g.comp f) R n = CohMap g R n ≫ CohMap f R n := by
  rw [CohMap, CohMap, CohMap, TopCat.ofHom_comp,
    Work.Cohomology.singularCohomologyMap_comp]

/-- The pullback is additive. -/
theorem CohMap_add {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂] (f : C(B₁, B₂))
    (R : Type) [CommRing R] (n : ℕ) (x y : Coh R n B₂) :
    (CohMap f R n).hom (x + y) = (CohMap f R n).hom x + (CohMap f R n).hom y :=
  map_add _ x y

/-- The pullback is `ℤ`-linear (in the form of compatibility with integer multiples). -/
theorem CohMap_zsmul {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂] (f : C(B₁, B₂))
    (n : ℕ) (k : ℤ) (x : Coh ℤ n B₂) : (CohMap f ℤ n).hom (k • x) = k • (CohMap f ℤ n).hom x :=
  map_zsmul _ k x

/-- **Homotopy invariance**: homotopic continuous maps induce the same pullback on singular
cohomology.  (`TopCat.Homotopy (TopCat.ofHom φ) (TopCat.ofHom φ')` is definitionally
`ContinuousMap.Homotopy φ φ'`.) -/
theorem CohMap_homotopic {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    {φ φ' : C(B₁, B₂)} (h : ContinuousMap.Homotopic φ φ') (R : Type) [CommRing R] (n : ℕ) :
    CohMap φ R n = CohMap φ' R n := by
  obtain ⟨H⟩ := h
  exact Work.Cohomology.homotopyInvariance R (TopCat.of B₁) (TopCat.of B₂) H n

/-- **The composite of the forgetful map out of a relative class with the restriction to `A` is
zero**: a class of the pair `(B,A)` restricts to zero on the subspace `A`. -/
theorem relToAbs_comp_restr (R : Type) [CommRing R] {B : Type} [TopologicalSpace B] (A : Set B)
    (n : ℕ) : relToAbs R A n ≫
      HomologicalComplex.homologyMap (Work.Cohomology.restr R (TopCat.of B) A) n = 0 := by
  rw [relToAbs, ← HomologicalComplex.homologyMap_comp,
    Work.Cohomology.relIncl_comp_restr R (TopCat.of B) A, HomologicalComplex.homologyMap_zero]

/-- The restriction map `H^n(B;R) → H^n(A;R)` of the pair `(B,A)`, as a pullback along the
inclusion of the subtype. -/
abbrev CohMap_subtype (R : Type) [CommRing R] {B : Type} [TopologicalSpace B] (A : Set B)
    (n : ℕ) : Coh R n B ⟶ Coh R n A :=
  CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(A, B)) R n

end

end Work.Thom
