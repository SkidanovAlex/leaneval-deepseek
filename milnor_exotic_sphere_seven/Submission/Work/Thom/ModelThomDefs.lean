import Mathlib
import Submission.Work.Thom.ModelGeometry
import Submission.Work.Thom.SuspensionStep
import Submission.Work.Thom.mixedCupC_pairNatural
import Submission.Work.Thom.CohHomotopyEquiv
import Submission.Work.Thom.relCohHomeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# The model Thom class of the trivial bundle: definitions

This module fixes the *model* in which the induction constructing the Thom class of the trivial
bundle `B × ℝⁿ → B` runs: the pair `(B × ℝⁿ, B × S^{n-1})` in the model fibre
`EuclideanSpace ℝ (Fin n)`, with the sphere `mSph n` removed.  `Work.Thom.ModelThom B n` is the
statement that this pair carries a class `τ` for which the *specific* map
`x ↦ π^*(x) ⌣ τ` (`Work.Thom.mixedCupC`, the module structure of the relative cohomology over the
absolute cohomology of the base) is bijective in every degree.

It also contains the general tools used to *transport* such a class across a map of pairs: the
homeomorphism `prodSubsetHomeo` between `B × S` and `{p : B × F | p.2 ∈ S}`, and
`cupMap_transfer`, which moves a model Thom class along a map `f` whose induced map on relative
cohomology is bijective and which commutes with the projections to the base.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-- The projection `B × F → B`, as a continuous map. -/
def projFst (B : Type) [TopologicalSpace B] (n : ℕ) :
    C(B × EuclideanSpace ℝ (Fin n), B) := ⟨Prod.fst, continuous_fst⟩

/-- **The model Thom class of rank `n` over `B`.**  The pair is `(B × ℝⁿ, B × S^{n-1})` (the sphere
`mSph n ⊆ EuclideanSpace ℝ (Fin n)` removed from the product with `B`), and the class `τ` is
required to make the *specific* cup map `x ↦ π^*(x) ⌣ τ` bijective in every degree. -/
def ModelThom (B : Type) [TopologicalSpace B] (n : ℕ) : Prop :=
  ∃ τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) {p | p.2 ∈ mSph n},
    ∀ k, Function.Bijective (fun x : Coh ℤ k B =>
      (mixedCupC ℤ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n} k n)
        ((CohMap (projFst B n) ℤ k).hom x) τ)

/-! ## The subset product homeomorphism -/

/-- **The canonical homeomorphism `B × S ≃ₜ {p : B × F | p.2 ∈ S}`** between the product of the
subtype `S` and the subtype of the product.  This is the bridge between the "product of subtypes"
and "subtype of product" forms in which the same pair of spaces occurs. -/
def prodSubsetHomeo (B : Type) [TopologicalSpace B] (F : Type) [TopologicalSpace F] (S : Set F) :
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

@[simp] theorem prodSubsetHomeo_apply (B : Type) [TopologicalSpace B] (F : Type)
    [TopologicalSpace F] (S : Set F) (q : B × S) :
    prodSubsetHomeo B F S q = ⟨(q.1, q.2.1), q.2.2⟩ := rfl

@[simp] theorem prodSubsetHomeo_symm_apply (B : Type) [TopologicalSpace B] (F : Type)
    [TopologicalSpace F] (S : Set F) (p : {p : B × F | p.2 ∈ S}) :
    (prodSubsetHomeo B F S).symm p = (p.1.1, ⟨p.1.2, p.2⟩) := rfl

/-! ## A homeomorphism of pairs induces a bijection on relative cohomology -/

/-- **A homeomorphism of pairs induces an isomorphism of relative cohomology.**  For a homeomorphism
`e : X ≃ₜ Y` carrying `A ⊆ X` onto `B ⊆ Y`, `relCohMap e A B : H^n(Y,B;R) → H^n(X,A;R)` is
bijective.  This is the explicit form of `Work.Thom.relCohHomeomorph` (which only records the
`Nonempty`-ness of the iso, hiding the map). -/
theorem bijective_relCohMap_of_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
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
    (relCohMap_comp' (X := X) (Y := Y) (Z := X) (A := A) (B := B) (C := A)
        (f := (e : C(X, Y))) (g := (e.symm : C(Y, X))) (hf := hf) (hg := hg)
        (R := R) (n := n) (fun x hx => hg ((e : C(X, Y)) x) (hf x hx))).trans
      ((relCohMap_congr' (f := (e.symm : C(Y, X)).comp (e : C(X, Y)))
          (f' := ContinuousMap.id X) A A hcompX
          (fun x hx => hg ((e : C(X, Y)) x) (hf x hx)) (fun _ hx => hx) R n).trans
        (relCohMap_id' A R n))
  have hcomp2 : CategoryTheory.CategoryStruct.comp (relCohMap (e : C(X, Y)) A B hf R n)
      (relCohMap (e.symm : C(Y, X)) B A hg R n) = 𝟙 (RelCoh R n Y B) :=
    (relCohMap_comp' (X := Y) (Y := X) (Z := Y) (A := B) (B := A) (C := B)
        (f := (e.symm : C(Y, X))) (g := (e : C(X, Y))) (hf := hg) (hg := hf)
        (R := R) (n := n) (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy))).trans
      ((relCohMap_congr' (f := (e : C(X, Y)).comp (e.symm : C(Y, X)))
          (f' := ContinuousMap.id Y) B B hcompY
          (fun y hy => hf ((e.symm : C(Y, X)) y) (hg y hy)) (fun _ hy => hy) R n).trans
        (relCohMap_id' B R n))
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

/-! ## Transporting a model Thom class along a map of pairs -/

/-- **Transport of the cup map along a map of pairs.**  Let `f : Y → X` carry `B ⊆ Y` into
`A ⊆ X` and suppose `relCohMap f : H^n(X,A;ℤ) → H^n(Y,B;ℤ)` is bijective in every degree, and `f`
commutes with the projections `πX : X → Z`, `πY : Y → Z` (`πX ∘ f = πY`).  Then for a class
`σ ∈ H^n(X,A;ℤ)` the cup map `x ↦ πX^*(x) ⌣ σ` on the `X` side is bijective in every degree **iff**
the cup map `x ↦ πY^*(x) ⌣ f^*(σ)` on the `Y` side is.

This is what moves a model Thom class through all the geometric identifications of the induction:
naturality of the mixed cup product (`Work.Thom.mixedCupC_pairNatural`) identifies the `Y`-cup map
with the composite of the `X`-cup map and `f^*`. -/
theorem cupMap_transfer_iff {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
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

/-- The forward form of `Work.Thom.cupMap_transfer_iff`: a model Thom class on the `X` side
descends to one on the `Y` side. -/
theorem cupMap_transfer_fwd {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(Y, X)) (A : Set X) (B : Set Y) (hf : ∀ y ∈ B, f y ∈ A)
    (hfbij : ∀ m, Function.Bijective (relCohMap f B A hf ℤ m).hom)
    (πX : C(X, Z)) (πY : C(Y, Z)) (hπ : πX.comp f = πY) (n : ℕ)
    (σ : RelCoh ℤ n X A)
    (hσ : ∀ k, Function.Bijective (fun x : Coh ℤ k Z =>
        (mixedCupC ℤ A k n) ((CohMap πX ℤ k).hom x) σ)) :
    ∀ k, Function.Bijective (fun x : Coh ℤ k Z =>
        (mixedCupC ℤ B k n) ((CohMap πY ℤ k).hom x) ((relCohMap f B A hf ℤ n).hom σ)) :=
  (cupMap_transfer_iff f A B hf hfbij πX πY hπ n σ).mp hσ

/-- The backward form of `Work.Thom.cupMap_transfer_iff`: a model Thom class on the `Y` side lifts
uniquely to one on the `X` side. -/
theorem cupMap_transfer_bwd {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
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
  exact ⟨σ, hσ, (cupMap_transfer_iff f A B hf hfbij πX πY hπ n σ).mpr (by rw [hσ]; exact hτ)⟩

end

end Work.Thom
