import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.StemsB.ThomRatShim

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The transfer toolkit of the Thom chapter, over an arbitrary coefficient ring

`Submission/Work/Thom/mixedCupC_pairNatural.lean` and `Submission/Work/Thom/ATools.lean` prove, over
`ℤ`, the naturality of the mixed cup product and the *transfer* of a Thom class along a map of pairs
(`x ↦ π^*(x) ⌣ σ`).  Their proofs use only coefficient-generic ingredients, so this file contains
the same statements and proofs over an arbitrary commutative ring `R`.  This is what the rational
(`ℚ`) model Thom induction needs; the `ℤ` originals are untouched.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.StemsB

open CategoryTheory

noncomputable section

variable (R : Type) [CommRing R]

/-! ## Naturality of the mixed Alexander–Whitney product -/

/-- **Naturality of the mixed Alexander–Whitney product on the relative cochains of a map of
pairs**, over `R`. -/
lemma relMapLM_cup_R {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (m n : ℕ)
    (a : Work.Cohomology.Cochain R (TopCat.toSSet.obj (TopCat.of Y)) m)
    (b : Work.Cohomology.relKern R (TopCat.of Y) B n)
    (hmem : Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of Y)) a b.1 ∈
      Work.Cohomology.relKern R (TopCat.of Y) B (m + n)) :
    ((Work.Cohomology.relMapLM R A B (TopCat.ofHom f) hf (m + n)
        ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of Y)) a b.1, hmem⟩).1) =
      Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of X))
        (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
            (ModuleCat.of R R)).f m).hom.dualMap a)
        ((Work.Cohomology.relMapLM R A B (TopCat.ofHom f) hf n b).1) := by
  rw [Work.Cohomology.relMapLM_coe, Work.Cohomology.relMapLM_coe]
  simp only [Work.Cohomology.dualChainMap_f_hom, Work.Cohomology.chainMap_f_eq]
  exact (Work.Cohomology.cupNatural R (TopCat.toSSet.map (TopCat.ofHom f)) a b.1).symm

/-- **Naturality of the mixed cup product under a map of pairs**, over `R`. -/
theorem mixedCupC_pairNaturalR {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (m n : ℕ)
    (x : Work.Thom.Coh R m Y) (z : Work.Thom.RelCoh R n Y B) :
    (Work.Thom.relCohMap f A B hf R (m + n)).hom ((Work.Thom.mixedCupC R B m n) x z)
      = (Work.Thom.mixedCupC R A m n) ((Work.Thom.CohMap f R m).hom x)
          ((Work.Thom.relCohMap f A B hf R n).hom z) := by
  change (Work.Thom.relCohMap f A B hf R (m + n)).hom
      ((Work.Cohomology.mixedCupR R (TopCat.of Y) B m n) x z)
    = (Work.Cohomology.mixedCupR R (TopCat.of X) A m n) ((Work.Thom.CohMap f R m).hom x)
        ((Work.Thom.relCohMap f A B hf R n).hom z)
  obtain ⟨a, ha, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf R
    (TopCat.toSSet.obj (TopCat.of Y)) m x
  obtain ⟨b, hb, rfl⟩ := Work.Cohomology.exists_relClassOf R (TopCat.of Y) B n z
  obtain ⟨hmemY, hcocY, hcupY⟩ :=
    Work.Cohomology.mixedCupR_apply R (TopCat.of Y) B m n a b ha hb
  have hCoh : (Work.Thom.CohMap f R m).hom
        (Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of Y)) a ha) =
      Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of X))
        (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
            (ModuleCat.of R R)).f m).hom.dualMap a)
        (Work.Cohomology.cochainDiff_dualMap_chainComplexMap R
          (TopCat.toSSet.map (TopCat.ofHom f)) a ha) :=
    Work.Cohomology.singularCohomologyMap_classOf R (TopCat.ofHom f) a ha
  have hRel := @Work.Cohomology.homologyMap_relComplexMap_relClassOf R _ (TopCat.of X)
    (TopCat.of Y) A B (TopCat.ofHom f) hf n b hb
  obtain ⟨hmemX, hcocX, hcupX⟩ := Work.Cohomology.mixedCupR_apply R (TopCat.of X) A m n
    (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of R R)).f m).hom.dualMap a)
    (@Work.Cohomology.relMapLM R _ (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom f) hf n b)
    (Work.Cohomology.cochainDiff_dualMap_chainComplexMap R
      (TopCat.toSSet.map (TopCat.ofHom f)) a ha)
    (@Work.Cohomology.relDiffLM_relMapLM R _ (TopCat.of X) (TopCat.of Y) A B
      (TopCat.ofHom f) hf n b hb)
  have hL1 := @Work.Cohomology.homologyMap_relComplexMap_relClassOf R _ (TopCat.of X)
    (TopCat.of Y) A B (TopCat.ofHom f) hf (m + n)
    ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of Y)) a b.1, hmemY⟩ hcocY
  have heq : (@Work.Cohomology.relMapLM R _ (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom f)
        hf (m + n)
        ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of Y)) a b.1, hmemY⟩)
      = ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of X))
          (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
              (ModuleCat.of R R)).f m).hom.dualMap a)
          ((@Work.Cohomology.relMapLM R _ (TopCat.of X) (TopCat.of Y) A B (TopCat.ofHom f)
            hf n b).1), hmemX⟩ := by
    apply Subtype.ext
    exact relMapLM_cup_R R f A B hf m n a b hmemY
  rw [hcupY, hL1, hCoh, hRel, hcupX]
  exact Work.Cohomology.relClassOf_congr R (TopCat.of X) A _ _ heq

/-! ## A homeomorphism of pairs induces a bijection on relative cohomology -/

/-- **A homeomorphism of pairs induces a bijection on relative cohomology**, over `R`. -/
theorem bijective_relCohMap_of_homeomorphR {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    Function.Bijective
      (Work.Thom.relCohMap (e : C(X, Y)) A B (fun x hx => (he x).mp hx) R n).hom := by
  have hf : ∀ x ∈ A, (e : C(X, Y)) x ∈ B := fun x hx => (he x).mp hx
  have hg : ∀ y ∈ B, (e.symm : C(Y, X)) y ∈ A :=
    fun y hy => (he (e.symm y)).mpr (by simpa using hy)
  have hcompY : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
    ext y; exact e.apply_symm_apply y
  have hcompX : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
    ext x; exact e.symm_apply_apply x
  have hcomp1 : CategoryTheory.CategoryStruct.comp
      (Work.Thom.relCohMap (e.symm : C(Y, X)) B A hg R n)
      (Work.Thom.relCohMap (e : C(X, Y)) A B hf R n) = 𝟙 (Work.Thom.RelCoh R n X A) :=
    (Work.Thom.relCohMap_compA A B A (e : C(X, Y)) (e.symm : C(Y, X)) hf hg
        (fun x hx => hg ((e : C(X, Y)) x) (hf x hx)) R n).trans
      ((Work.Thom.relCohMap_congrA A A hcompX (fun x hx => hg ((e : C(X, Y)) x) (hf x hx))
          (fun _ hx => hx) R n).trans
        (Work.Thom.relCohMap_idA A R n))
  have hcomp2 : CategoryTheory.CategoryStruct.comp
      (Work.Thom.relCohMap (e : C(X, Y)) A B hf R n)
      (Work.Thom.relCohMap (e.symm : C(Y, X)) B A hg R n) = 𝟙 (Work.Thom.RelCoh R n Y B) :=
    (Work.Thom.relCohMap_compA B A B (e.symm : C(Y, X)) (e : C(X, Y)) hg hf
        (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy)) R n).trans
      ((Work.Thom.relCohMap_congrA B B hcompY (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy))
          (fun _ hy => hy) R n).trans
        (Work.Thom.relCohMap_idA B R n))
  have hlin1 : (Work.Thom.relCohMap (e : C(X, Y)) A B hf R n).hom.comp
      (Work.Thom.relCohMap (e.symm : C(Y, X)) B A hg R n).hom = LinearMap.id := by
    have := congrArg (fun φ : Work.Thom.RelCoh R n X A ⟶ Work.Thom.RelCoh R n X A => φ.hom) hcomp1
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  have hlin2 : (Work.Thom.relCohMap (e.symm : C(Y, X)) B A hg R n).hom.comp
      (Work.Thom.relCohMap (e : C(X, Y)) A B hf R n).hom = LinearMap.id := by
    have := congrArg (fun φ : Work.Thom.RelCoh R n Y B ⟶ Work.Thom.RelCoh R n Y B => φ.hom) hcomp2
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using this
  constructor
  · intro a b hab
    have ha := LinearMap.congr_fun hlin2 a
    have hb := LinearMap.congr_fun hlin2 b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [hab] at ha
    exact ha.symm.trans hb
  · intro b
    exact ⟨(Work.Thom.relCohMap (e.symm : C(Y, X)) B A hg R n).hom b,
      LinearMap.congr_fun hlin1 b⟩

/-! ## Transporting a Thom class along a map of pairs -/

/-- **Transport of the cup map along a map of pairs**, over `R`. -/
theorem cupMap_transfer_iffR {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (hfbij : ∀ m, Function.Bijective (Work.Thom.relCohMap f B A hf R m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (σ : Work.Thom.RelCoh R n X A) :
    (∀ k, Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R A k n) ((Work.Thom.CohMap πX R k).hom x) σ)) ↔
      (∀ k, Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R B k n) ((Work.Thom.CohMap πY R k).hom x)
          ((Work.Thom.relCohMap f B A hf R n).hom σ))) := by
  have hCoh : ∀ (k : ℕ) (x : Work.Thom.Coh R k Z),
      (Work.Thom.CohMap f R k).hom ((Work.Thom.CohMap πX R k).hom x)
      = (Work.Thom.CohMap πY R k).hom x := by
    intro k x
    have h := LinearMap.congr_fun (Work.Thom.CohMap_linear_comp f πX R k) x
    simp only [LinearMap.comp_apply] at h
    rw [h, hπ]
  constructor
  · intro h k
    have key : ∀ x : Work.Thom.Coh R k Z,
        (Work.Thom.mixedCupC R B k n) ((Work.Thom.CohMap πY R k).hom x)
            ((Work.Thom.relCohMap f B A hf R n).hom σ)
          = (Work.Thom.relCohMap f B A hf R (k + n)).hom
              ((Work.Thom.mixedCupC R A k n) ((Work.Thom.CohMap πX R k).hom x) σ) := by
      intro x
      rw [mixedCupC_pairNaturalR R f B A hf k n ((Work.Thom.CohMap πX R k).hom x) σ, hCoh k x]
    rw [funext key]
    exact (hfbij (k + n)).comp (h k)
  · intro h k
    have key : ∀ x : Work.Thom.Coh R k Z,
        (Work.Thom.mixedCupC R B k n) ((Work.Thom.CohMap πY R k).hom x)
            ((Work.Thom.relCohMap f B A hf R n).hom σ)
          = (Work.Thom.relCohMap f B A hf R (k + n)).hom
              ((Work.Thom.mixedCupC R A k n) ((Work.Thom.CohMap πX R k).hom x) σ) := by
      intro x
      rw [mixedCupC_pairNaturalR R f B A hf k n ((Work.Thom.CohMap πX R k).hom x) σ, hCoh k x]
    refine ⟨fun a b hab => ?_, fun b => ?_⟩
    · have h2 := congrArg (fun z => (Work.Thom.relCohMap f B A hf R (k + n)).hom z) hab
      rw [← key a, ← key b] at h2
      exact (h k).1 h2
    · obtain ⟨x, hx⟩ := (h k).2 ((Work.Thom.relCohMap f B A hf R (k + n)).hom b)
      exact ⟨x, (hfbij (k + n)).1 (by dsimp only at hx; rw [key x] at hx; exact hx)⟩

/-- The forward form of `cupMap_transfer_iffR`. -/
theorem cupMap_transfer_fwdR {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (hfbij : ∀ m, Function.Bijective (Work.Thom.relCohMap f B A hf R m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (σ : Work.Thom.RelCoh R n X A)
    (hσ : ∀ k, Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R A k n) ((Work.Thom.CohMap πX R k).hom x) σ)) :
    ∀ k, Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R B k n) ((Work.Thom.CohMap πY R k).hom x)
          ((Work.Thom.relCohMap f B A hf R n).hom σ)) :=
  (cupMap_transfer_iffR R f A B hf hfbij πX πY hπ n σ).mp hσ

/-- The backward form of `cupMap_transfer_iffR`. -/
theorem cupMap_transfer_bwdR {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (hfbij : ∀ m, Function.Bijective (Work.Thom.relCohMap f B A hf R m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (τ : Work.Thom.RelCoh R n Y B)
    (hτ : ∀ k, Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R B k n) ((Work.Thom.CohMap πY R k).hom x) τ)) :
    ∃ τ' : Work.Thom.RelCoh R n X A,
      (Work.Thom.relCohMap f B A hf R n).hom τ' = τ ∧
      ∀ k, Function.Bijective (fun x : Work.Thom.Coh R k Z =>
        (Work.Thom.mixedCupC R A k n) ((Work.Thom.CohMap πX R k).hom x) τ') := by
  obtain ⟨σ, hσ⟩ := (hfbij n).2 τ
  exact ⟨σ, hσ, (cupMap_transfer_iffR R f A B hf hfbij πX πY hπ n σ).mpr (by rw [hσ]; exact hτ)⟩

/-- `(-1)^k` is its own inverse, over an arbitrary commutative ring. -/
theorem negOnePow_mul_selfR (k : ℕ) : ((-1 : R) ^ k) * ((-1 : R) ^ k) = 1 := by
  rw [← pow_add, show k + k = 2 * k from (Nat.two_mul k).symm, pow_mul,
    show ((-1 : R)) ^ 2 = 1 by norm_num, one_pow]

end

end Work.StemsB
