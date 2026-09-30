import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.Pullback
import Submission.Work.Thom.mixedCupC_pairNatural
import Submission.Work.Thom.CohHomotopyEquiv

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# The transfer toolkit, in the island of the relative Mayer–Vietoris sequence

**Why this module exists.**  `Submission/Work/` is (as it stands) split into several mutually
incompatible *islands*, because different files declare the same names — Lean then refuses to
elaborate any module whose transitive imports contain both:

| duplicated declaration | declared in | declared in |
|---|---|---|
| `Work.Cohomology.dualZ` | `Cohomology/localCohomology.lean` | `Cohomology/dualZ.lean` |
| `Work.Cohomology.Yt` | `Cohomology/prod_sphere_aux.lean` | `Cohomology/CompatTrans/proj_pair_injective.lean` |
| `Work.Cohomology.ovlTopX` (and 8 more) | `Cohomology/Crux/ovlRestrictionSurjective.lean` | `Cohomology/Crux/vkCruxRestr.lean` |

The files of `Submission/Work/TangentClasses/`, `Submission/Work/Milnor/CappedManifold.lean`,
`Submission/Work/SignatureBordism/`, `Submission/Work/CharacteristicClasses/` and
`Submission/Work/Thom/Interface.lean` — i.e. everything the exotic-`7`-sphere endgame consumes —
all live in the island containing `Cohomology/localCohomology.lean`,
`CompatTrans/proj_pair_injective.lean` and `Crux/ovlRestrictionSurjective.lean`, and *outside* the
two other duplications.  This module is written to live in exactly that island.

The **transfer of a Thom class along a map of pairs** — the tool by which local Thom data over a
chart of the trivial bundle is transported to a chart of a general bundle — was previously available
only as `Work.Thom.cupMap_transfer_iff` / `_fwd` / `_bwd` (in `Submission/Work/Thom/ModelThomDefs.lean`,
island of `dualZ`), together with the preliminary `Work.Thom.bijective_relCohMap_of_homeomorph`.  The
lemmas below are *copies of that material* under the name suffix `A`; the proofs are the same and
they use only `Work.Thom.Cohomology`, the functoriality of `relComplexMap`, and the naturality of
the mixed cup product (`Work.Thom.mixedCupC_pairNatural`) — all of them in the island above.

Main results:

* `Work.Thom.relComplexMap_compA`, `relComplexMap_hcongrA`, `relComplexMap_congrA`,
  `relComplexMap_idA` — functoriality of the pair map on relative cochains, for arbitrary
  coefficients;
* `Work.Thom.relCohMap_compA`, `relCohMap_congrA`, `relCohMap_idA` — the induced functoriality of
  the pullback on relative cohomology (copies of `relCohMap_comp'`, `relCohMap_congr'`,
  `relCohMap_id'` of the group-`B` module `relCohHomeomorph.lean` and of `relCohMap_id`);
* `Work.Thom.projFstA`, `prodSubsetHomeoA` — the projection of a product and the identification of
  `B × S` with the subtype `{p : B × F | p.2 ∈ S}` (copies of `projFst`, `prodSubsetHomeo`);
* `Work.Thom.bijective_relCohMap_of_homeomorphA` — a homeomorphism of pairs induces a bijection on
  relative cohomology;
* `Work.Thom.cupMap_transfer_iffA`, `cupMap_transfer_fwdA`, `cupMap_transfer_bwdA` — the transport
  of the bijectivity of the cup map `x ↦ π^*(x) ⌣ σ` along a map of pairs that is an isomorphism on
  relative cohomology and commutes with the projections to the base.
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Functoriality of the relative cochain complex -/

/-- **Chain-level functoriality of the pair map** (composition), for arbitrary coefficients. -/
theorem relComplexMap_compA {X₁ X₂ X₃ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (A₃ : Set X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hf : ∀ x ∈ A₁, f x ∈ A₂) (hg : ∀ y ∈ A₂, g y ∈ A₃)
    (R : Type) [CommRing R] :
    Work.Cohomology.relComplexMap R A₁ A₃ (f ≫ g) (fun x hx => hg (f x) (hf x hx))
      = Work.Cohomology.relComplexMap R A₂ A₃ g hg
        ≫ Work.Cohomology.relComplexMap R A₁ A₂ f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, Work.Cohomology.relComplexMap_f, Work.Cohomology.relComplexMap_f,
    Work.Cohomology.relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.comp_apply,
    Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_comp, HomologicalComplex.comp_f]
  rfl

/-- The pair map does not depend on the proof that the first set is carried into the second. -/
theorem relComplexMap_hcongrA {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h h' : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂) (R : Type) [CommRing R] :
    Work.Cohomology.relComplexMap R A₁ A₂ f h = Work.Cohomology.relComplexMap R A₁ A₂ f h' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The pair map depends only on the underlying map. -/
theorem relComplexMap_congrA {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) {f f' : X₁ ⟶ X₂}
    (h : f = f') (hf : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂)
    (hf' : ∀ x ∈ A₁, (ConcreteCategory.hom f') x ∈ A₂) (R : Type) [CommRing R] :
    Work.Cohomology.relComplexMap R A₁ A₂ f hf
      = Work.Cohomology.relComplexMap R A₁ A₂ f' hf' := by
  subst h
  exact relComplexMap_hcongrA A₁ A₂ f hf hf' R

/-- **The pair map is functorial: the identity.** -/
theorem relComplexMap_idA {X : TopCat} (A : Set X) (h : ∀ x ∈ A, (𝟙 X : X ⟶ X) x ∈ A)
    (R : Type) [CommRing R] :
    Work.Cohomology.relComplexMap R A A (𝟙 X) h = 𝟙 (Work.Cohomology.relComplex R X A) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [Work.Cohomology.relComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_id,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rfl

/-! ## Functoriality of the pullback on relative cohomology -/

/-- **Functoriality of the pullback of relative cohomology.** -/
theorem relCohMap_compA {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (B : Set Y) (C : Set Z) (f : C(X, Y)) (g : C(Y, Z))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ y ∈ B, g y ∈ C) (hgf : ∀ x ∈ A, g (f x) ∈ C)
    (R : Type) [CommRing R] (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (relCohMap g B C hg R n) (relCohMap f A B hf R n)
      = relCohMap (g.comp f) A C hgf R n := by
  have key : CategoryTheory.CategoryStruct.comp
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of Y) (X₂ := TopCat.of Z) R B C
        (TopCat.ofHom g) hg)
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B
        (TopCat.ofHom f) hf)
    = Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Z) R A C
        (TopCat.ofHom (g.comp f)) hgf := by
    rw [← relComplexMap_compA (X₁ := TopCat.of X) (X₂ := TopCat.of Y) (X₃ := TopCat.of Z)
      A B C (TopCat.ofHom f) (TopCat.ofHom g) hf hg (R := R)]
    exact relComplexMap_congrA A C (TopCat.ofHom_comp f g).symm
      (fun x hx => hg (f x) (hf x hx)) hgf R
  have hg' : relCohMap g B C hg R n = HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of Y) (X₂ := TopCat.of Z) R B C
        (TopCat.ofHom g) hg) n := rfl
  have hf' : relCohMap f A B hf R n = HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) R A B
        (TopCat.ofHom f) hf) n := rfl
  have hgf' : relCohMap (g.comp f) A C hgf R n = HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Z) R A C
        (TopCat.ofHom (g.comp f)) hgf) n := rfl
  rw [hg', hf', hgf', ← HomologicalComplex.homologyMap_comp, key]

/-- **The pullback of relative cohomology only depends on the underlying continuous map.** -/
theorem relCohMap_congrA {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f f' : C(X, Y)}
    (A : Set X) (B : Set Y) (h : f = f') (hf : ∀ x ∈ A, f x ∈ B) (hf' : ∀ x ∈ A, f' x ∈ B)
    (R : Type) [CommRing R] (n : ℕ) :
    relCohMap f A B hf R n = relCohMap f' A B hf' R n := by
  show HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
      (X₂ := TopCat.of Y) R A B (TopCat.ofHom f) hf) n
    = HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
      (X₂ := TopCat.of Y) R A B (TopCat.ofHom f') hf') n
  rw [relComplexMap_congrA A B
    (congrArg (fun f : C(X, Y) => (TopCat.ofHom f : TopCat.of X ⟶ TopCat.of Y)) h) hf hf' R]

/-- **The pullback of relative cohomology along the identity of pairs is the identity.** -/
theorem relCohMap_idA {X : Type} [TopologicalSpace X] (A : Set X) (R : Type) [CommRing R]
    (n : ℕ) :
    relCohMap (ContinuousMap.id X) A A (fun _ h => h) R n
      = CategoryTheory.CategoryStruct.id (RelCoh R n X A) := by
  have hdual : Work.Cohomology.dualChainMap R (TopCat.of X) (TopCat.of X)
      (TopCat.ofHom (ContinuousMap.id X))
      = 𝟙 (Work.Cohomology.singularCochainComplex R (TopCat.of X)) := by
    rw [TopCat.ofHom_id, Work.Cohomology.dualChainMap_id]
  have key : ∀ (h : ∀ x ∈ A,
        (TopCat.ofHom (ContinuousMap.id X) : TopCat.of X ⟶ TopCat.of X) x ∈ A),
      Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of X) R A A
        (TopCat.ofHom (ContinuousMap.id X)) h
        = 𝟙 (Work.Cohomology.relComplex R (TopCat.of X) A) := by
    intro h
    apply HomologicalComplex.hom_ext
    intro k
    rw [Work.Cohomology.relComplexMap_f]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ModuleCat.hom_ofHom, Work.Cohomology.relMapLM_coe, hdual,
      HomologicalComplex.id_f, ModuleCat.hom_id]
    exact congrArg Subtype.val rfl
  show HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
      (X₂ := TopCat.of X) R A A (TopCat.ofHom (ContinuousMap.id X)) (fun _ h => h)) n
    = CategoryTheory.CategoryStruct.id (Work.Cohomology.relCohomology R (TopCat.of X) A n)
  exact (congrArg (fun φ => HomologicalComplex.homologyMap φ n) (key _)).trans
    (HomologicalComplex.homologyMap_id (Work.Cohomology.relComplex R (TopCat.of X) A) n)

/-! ## The projection of a product and the subset-product homeomorphism -/

/-- The projection `B × F → B` of a product, as a continuous map. -/
def projFstA (B : Type) [TopologicalSpace B] (n : ℕ) :
    C(B × EuclideanSpace ℝ (Fin n), B) := ⟨Prod.fst, continuous_fst⟩

/-- **The canonical homeomorphism `B × S ≃ₜ {p : B × F | p.2 ∈ S}`.** -/
def prodSubsetHomeoA (B : Type) [TopologicalSpace B] (F : Type) [TopologicalSpace F] (S : Set F) :
    (B × S) ≃ₜ {p : B × F | p.2 ∈ S} where
  toFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
  invFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
  left_inv := fun q => by ext <;> rfl
  right_inv := fun p => by ext <;> rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    refine continuous_fst.comp continuous_subtype_val |>.prodMk ?_
    exact Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _

@[simp] theorem prodSubsetHomeoA_apply (B : Type) [TopologicalSpace B] (F : Type)
    [TopologicalSpace F] (S : Set F) (q : B × S) :
    prodSubsetHomeoA B F S q = ⟨(q.1, q.2.1), q.2.2⟩ := rfl

@[simp] theorem prodSubsetHomeoA_symm_apply (B : Type) [TopologicalSpace B] (F : Type)
    [TopologicalSpace F] (S : Set F) (p : {p : B × F | p.2 ∈ S}) :
    (prodSubsetHomeoA B F S).symm p = (p.1.1, ⟨p.1.2, p.2⟩) := rfl

/-! ## A homeomorphism of pairs induces a bijection on relative cohomology -/

/-- **A homeomorphism of pairs induces an isomorphism of relative cohomology.** -/
theorem bijective_relCohMap_of_homeomorphA {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) (R : Type) [CommRing R]
    (n : ℕ) :
    Function.Bijective (relCohMap (e : C(X, Y)) A B (fun x hx => (he x).mp hx) R n).hom := by
  have hf : ∀ x ∈ A, (e : C(X, Y)) x ∈ B := fun x hx => (he x).mp hx
  have hg : ∀ y ∈ B, (e.symm : C(Y, X)) y ∈ A :=
    fun y hy => (he (e.symm y)).mpr (by simpa using hy)
  have hcompY : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
    ext y; exact e.apply_symm_apply y
  have hcompX : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
    ext x; exact e.symm_apply_apply x
  have hcomp1 : CategoryTheory.CategoryStruct.comp (relCohMap (e.symm : C(Y, X)) B A hg R n)
      (relCohMap (e : C(X, Y)) A B hf R n) = 𝟙 (RelCoh R n X A) :=
    (relCohMap_compA A B A (e : C(X, Y)) (e.symm : C(Y, X)) hf hg
        (fun x hx => hg ((e : C(X, Y)) x) (hf x hx)) R n).trans
      ((relCohMap_congrA A A hcompX (fun x hx => hg ((e : C(X, Y)) x) (hf x hx))
          (fun _ hx => hx) R n).trans
        (relCohMap_idA A R n))
  have hcomp2 : CategoryTheory.CategoryStruct.comp (relCohMap (e : C(X, Y)) A B hf R n)
      (relCohMap (e.symm : C(Y, X)) B A hg R n) = 𝟙 (RelCoh R n Y B) :=
    (relCohMap_compA B A B (e.symm : C(Y, X)) (e : C(X, Y)) hg hf
        (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy)) R n).trans
      ((relCohMap_congrA B B hcompY (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy))
          (fun _ hy => hy) R n).trans
        (relCohMap_idA B R n))
  have hlin1 : (relCohMap (e : C(X, Y)) A B hf R n).hom.comp
      (relCohMap (e.symm : C(Y, X)) B A hg R n).hom = LinearMap.id := by
    have := congrArg (fun φ : RelCoh R n X A ⟶ RelCoh R n X A => φ.hom) hcomp1
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  have hlin2 : (relCohMap (e.symm : C(Y, X)) B A hg R n).hom.comp
      (relCohMap (e : C(X, Y)) A B hf R n).hom = LinearMap.id := by
    have := congrArg (fun φ : RelCoh R n Y B ⟶ RelCoh R n Y B => φ.hom) hcomp2
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  constructor
  · intro a b hab
    have ha := LinearMap.congr_fun hlin2 a
    have hb := LinearMap.congr_fun hlin2 b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [hab] at ha
    exact ha.symm.trans hb
  · intro b
    exact ⟨(relCohMap (e.symm : C(Y, X)) B A hg R n).hom b, LinearMap.congr_fun hlin1 b⟩

/-! ## Transporting a Thom class along a map of pairs -/

/-- **Transport of the cup map along a map of pairs.** -/
theorem cupMap_transfer_iffA {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (hfbij : ∀ m, Function.Bijective (relCohMap f B A hf ℤ m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (σ : RelCoh ℤ n X A) :
    (∀ k, Function.Bijective (fun x : Coh ℤ k Z =>
        (mixedCupC ℤ A k n) ((CohMap πX ℤ k).hom x) σ)) ↔
      (∀ k, Function.Bijective (fun x : Coh ℤ k Z =>
        (mixedCupC ℤ B k n) ((CohMap πY ℤ k).hom x) ((relCohMap f B A hf ℤ n).hom σ))) := by
  have hCoh : ∀ (k : ℕ) (x : Coh ℤ k Z), (CohMap f ℤ k).hom ((CohMap πX ℤ k).hom x)
      = (CohMap πY ℤ k).hom x := by
    intro k x
    have h := LinearMap.congr_fun (CohMap_linear_comp f πX ℤ k) x
    simp only [LinearMap.comp_apply] at h
    rw [h, hπ]
  constructor
  · intro h k
    have key : ∀ x : Coh ℤ k Z,
        (mixedCupC ℤ B k n) ((CohMap πY ℤ k).hom x) ((relCohMap f B A hf ℤ n).hom σ)
          = (relCohMap f B A hf ℤ (k + n)).hom
              ((mixedCupC ℤ A k n) ((CohMap πX ℤ k).hom x) σ) := by
      intro x
      rw [mixedCupC_pairNatural f B A hf k n ((CohMap πX ℤ k).hom x) σ, hCoh k x]
    rw [funext key]
    exact (hfbij (k + n)).comp (h k)
  · intro h k
    have key : ∀ x : Coh ℤ k Z,
        (mixedCupC ℤ B k n) ((CohMap πY ℤ k).hom x) ((relCohMap f B A hf ℤ n).hom σ)
          = (relCohMap f B A hf ℤ (k + n)).hom
              ((mixedCupC ℤ A k n) ((CohMap πX ℤ k).hom x) σ) := by
      intro x
      rw [mixedCupC_pairNatural f B A hf k n ((CohMap πX ℤ k).hom x) σ, hCoh k x]
    refine ⟨fun a b hab => ?_, fun b => ?_⟩
    · have h2 := congrArg (fun z => (relCohMap f B A hf ℤ (k + n)).hom z) hab
      rw [← key a, ← key b] at h2
      exact (h k).1 h2
    · obtain ⟨x, hx⟩ := (h k).2 ((relCohMap f B A hf ℤ (k + n)).hom b)
      exact ⟨x, (hfbij (k + n)).1 (by dsimp only at hx; rw [key x] at hx; exact hx)⟩

/-- The forward form of `Work.Thom.cupMap_transfer_iffA`. -/
theorem cupMap_transfer_fwdA {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (hfbij : ∀ m, Function.Bijective (relCohMap f B A hf ℤ m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (σ : RelCoh ℤ n X A)
    (hσ : ∀ k, Function.Bijective (fun x : Coh ℤ k Z =>
        (mixedCupC ℤ A k n) ((CohMap πX ℤ k).hom x) σ)) :
    ∀ k, Function.Bijective (fun x : Coh ℤ k Z =>
        (mixedCupC ℤ B k n) ((CohMap πY ℤ k).hom x) ((relCohMap f B A hf ℤ n).hom σ)) :=
  (cupMap_transfer_iffA f A B hf hfbij πX πY hπ n σ).mp hσ

/-- The backward form of `Work.Thom.cupMap_transfer_iffA`. -/
theorem cupMap_transfer_bwdA {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (hfbij : ∀ m, Function.Bijective (relCohMap f B A hf ℤ m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (τ : RelCoh ℤ n Y B)
    (hτ : ∀ k, Function.Bijective (fun x : Coh ℤ k Z =>
        (mixedCupC ℤ B k n) ((CohMap πY ℤ k).hom x) τ)) :
    ∃ τ' : RelCoh ℤ n X A,
      (relCohMap f B A hf ℤ n).hom τ' = τ ∧
      ∀ k, Function.Bijective (fun x : Coh ℤ k Z =>
        (mixedCupC ℤ A k n) ((CohMap πX ℤ k).hom x) τ') := by
  obtain ⟨σ, hσ⟩ := (hfbij n).2 τ
  exact ⟨σ, hσ, (cupMap_transfer_iffA f A B hf hfbij πX πY hπ n σ).mpr (by rw [hσ]; exact hτ)⟩

end

end Work.Thom
