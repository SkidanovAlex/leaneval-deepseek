import Mathlib
import Submission.Work.Thom.modelSphereBundleStep
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.ATools

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# The two hypotheses of the suspension step for the model sphere bundle, with coefficients in `R`

This is `Work.Thom.modelSphereBundleStep` with the coefficient ring `ℤ` promoted to an arbitrary
commutative ring `R`.  The proof is verbatim the same: every ingredient
(`CohMap_linear_comp`, `bijective_CohMap_of_homotopyEquiv`, `CohMap_id`) is already stated for an
arbitrary coefficient ring `R`, and the geometry (`mLowerContractible`) is coefficient-free.
-/

namespace Work.StemsB

open Work.Thom

noncomputable section

/-- **The two hypotheses of the suspension step for the model sphere bundle, with `R` coefficients.**
Let `A := B × sph (n+1)` be the sphere bundle of rank `n+1` as a subspace of `B × ℝ^{n+1}`, and let
`A₁ ⊆ A` be the part lying over the lower region `mLower n`.  Then (i) the restriction
`H^*(B × ℝ^{n+1};R) → H^*(A;R)` is injective, and (ii) the composite
`H^*(B × ℝ^{n+1};R) → H^*(A;R) → H^*(A₁;R)` is bijective. -/
theorem modelSphereBundleStepRat (R : Type) [CommRing R] (B : Type) [TopologicalSpace B] (n : ℕ) :
    (∀ m, Function.Injective
        ((Work.Thom.CohMap (Work.Thom.subtypeMap {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ Work.Thom.mSph (n + 1)}) R m).hom))
      ∧ (∀ m, Function.Bijective
        (((Work.Thom.CohMap (Work.Thom.subtypeMap {q : {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ Work.Thom.mSph (n + 1)} | ((q : B × EuclideanSpace ℝ (Fin (n + 1))).2) ∈ Work.Thom.mLower n}) R m).hom).comp
          ((Work.Thom.CohMap (Work.Thom.subtypeMap {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ Work.Thom.mSph (n + 1)}) R m).hom))) := by
  set S1 : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mSph (n + 1)} with hS1
  set S2 : Set S1 := {q : S1 | ((q : B × EuclideanSpace ℝ (Fin (n + 1))).2) ∈ mLower n} with hS2
  set A1 : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ mLower n} with hA1
  constructor
  · -- (i) the restriction `H^*(X) → H^*(A)` is injective
    intro m
    show Function.Injective ((CohMap (subtypeMap S1) R m).hom)
    -- a point of the sphere, to build a section of the sphere bundle over `B`
    let p0 : EuclideanSpace ℝ (Fin (n + 1)) := Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1)
    have hp0 : p0 ∈ mSph (n + 1) := by
      show ‖p0‖ = 1
      have h : ‖p0‖ ^ 2 = 1 := by
        show ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1)‖ ^ 2 = 1
        rw [Work.Morse.snocLp_norm_sq]; norm_num
      nlinarith [norm_nonneg p0]
    -- the projection `X → B` is a homotopy equivalence (the fibre is contractible)
    let projX : C(B × EuclideanSpace ℝ (Fin (n + 1)), B) := ⟨Prod.fst, continuous_fst⟩
    let sX : C(B, B × EuclideanSpace ℝ (Fin (n + 1))) := ⟨fun b => (b, p0), by fun_prop⟩
    have key : ∀ x : B × EuclideanSpace ℝ (Fin (n + 1)), (sX.comp projX) x = (x.1, p0) := by
      intro x
      simp only [ContinuousMap.comp_apply]
      change sX x.1 = (x.1, p0)
      rfl
    have h1 : (sX.comp projX).Homotopic
        (ContinuousMap.id (B × EuclideanSpace ℝ (Fin (n + 1)))) := by
      refine ⟨⟨fun tx : unitInterval × (B × EuclideanSpace ℝ (Fin (n + 1))) =>
          (tx.2.1, (1 - (tx.1 : ℝ)) • p0 + (tx.1 : ℝ) • tx.2.2), by fun_prop⟩, ?_, ?_⟩
      · intro x; rw [key x]; simp
      · intro x; apply Prod.ext <;> simp
    have h2 : (projX.comp sX).Homotopic (ContinuousMap.id B) := by
      have heq : projX.comp sX = ContinuousMap.id B := by ext b; rfl
      simpa [heq] using ContinuousMap.Homotopic.refl (ContinuousMap.id B)
    let HE : ContinuousMap.HomotopyEquiv (B × EuclideanSpace ℝ (Fin (n + 1))) B :=
      ContinuousMap.HomotopyEquiv.mk projX sX h1 h2
    have hbij : Function.Bijective (CohMap projX R m).hom :=
      bijective_CohMap_of_homotopyEquiv HE R m
    -- the projection of the sphere bundle to `B` has a section, so it is injective on cohomology
    let projA : C(↥S1, B) := projX.comp (subtypeMap S1)
    let sA : C(B, ↥S1) :=
      ⟨fun b => ⟨(b, p0), hp0⟩, Continuous.subtype_mk (continuous_id.prodMk continuous_const)
        (fun _ => hp0)⟩
    have hinj_projA : Function.Injective (CohMap projA R m).hom := by
      have hcomp : (CohMap sA R m).hom.comp (CohMap projA R m).hom
          = (CohMap (projA.comp sA) R m).hom := CohMap_linear_comp sA projA R m
      have hid : projA.comp sA = ContinuousMap.id B := by ext b; rfl
      rw [hid, CohMap_id] at hcomp
      intro x y hxy
      have hx := LinearMap.congr_fun hcomp x
      have hy := LinearMap.congr_fun hcomp y
      simp only [LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at hx hy
      rw [hxy] at hx
      exact hx.symm.trans hy
    have hkey : ∀ z, (CohMap (subtypeMap S1) R m).hom ((CohMap projX R m).hom z)
        = (CohMap projA R m).hom z := by
      intro z
      have := LinearMap.congr_fun (CohMap_linear_comp (subtypeMap S1) projX R m) z
      simpa only [LinearMap.comp_apply] using this
    intro x y hxy
    obtain ⟨x', rfl⟩ := hbij.2 x
    obtain ⟨y', rfl⟩ := hbij.2 y
    have hQ : (CohMap projA R m).hom x' = (CohMap projA R m).hom y' := by
      rw [← hkey x', ← hkey y']; exact hxy
    rw [hinj_projA hQ]
  · -- (ii) the composite `H^*(X) → H^*(A) → H^*(A₁)` is bijective
    intro m
    show Function.Bijective
      (((CohMap (subtypeMap S2) R m).hom).comp ((CohMap (subtypeMap S1) R m).hom))
    let cc : C(↥S2, B × EuclideanSpace ℝ (Fin (n + 1))) :=
      (subtypeMap S1).comp (subtypeMap S2)
    have hcomp : ((CohMap (subtypeMap S2) R m).hom).comp
          ((CohMap (subtypeMap S1) R m).hom) = (CohMap cc R m).hom :=
      CohMap_linear_comp (subtypeMap S2) (subtypeMap S1) R m
    rw [hcomp]
    -- the homeomorphism `A₁ ↪ A ↪ X` is the inclusion `{p | p.2 ∈ mLower n} ↪ X`
    have hsub : mLower n ⊆ mSph (n + 1) := mLower_subset_mSph n
    have hf1 : Continuous (fun p : ↥A1 => (p.1 : B × EuclideanSpace ℝ (Fin (n + 1)))) :=
      continuous_subtype_val
    have hf2 : Continuous (fun q : ↥S2 => ((q : ↥S1) : B × EuclideanSpace ℝ (Fin (n + 1)))) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hcont : Continuous (fun p : ↥A1 => (⟨⟨p.1, hsub p.2⟩, p.2⟩ : ↥S2)) :=
      Continuous.subtype_mk (Continuous.subtype_mk hf1 (fun p => hsub p.2)) (fun p => p.2)
    have hcont2 : Continuous (fun q : ↥S2 =>
        (⟨(q : B × EuclideanSpace ℝ (Fin (n + 1))), q.2⟩ : ↥A1)) :=
      Continuous.subtype_mk hf2 (fun q => q.2)
    let einv : C(↥A1, ↥S2) := ⟨fun p => ⟨⟨p.1, hsub p.2⟩, p.2⟩, hcont⟩
    let e : C(↥S2, ↥A1) := ⟨fun q => ⟨(q : B × EuclideanSpace ℝ (Fin (n + 1))), q.2⟩, hcont2⟩
    have he_left : einv.comp e = ContinuousMap.id ↥S2 := by
      apply ContinuousMap.ext; intro q; apply Subtype.ext; apply Subtype.ext; rfl
    have he_right : e.comp einv = ContinuousMap.id ↥A1 := by
      apply ContinuousMap.ext; intro p; apply Subtype.ext; rfl
    have h1' : (einv.comp e).Homotopic (ContinuousMap.id ↥S2) := by rw [he_left]
    have h2' : (e.comp einv).Homotopic (ContinuousMap.id ↥A1) := by rw [he_right]
    let HE' : ContinuousMap.HomotopyEquiv ↥S2 ↥A1 :=
      ContinuousMap.HomotopyEquiv.mk e einv h1' h2'
    have hbijE : Function.Bijective (CohMap e R m).hom :=
      bijective_CohMap_of_homotopyEquiv HE' R m
    -- the inclusion of the lower disc into `X` is a homotopy equivalence
    obtain ⟨HEA1, hHEA1⟩ := subtypeMap_mLower_homotopyEquiv B n
    have hbijA1 : Function.Bijective (CohMap (subtypeMap A1) R m).hom := by
      have h2 := bijective_CohMap_of_homotopyEquiv HEA1 R m
      rwa [hHEA1] at h2
    have hceq : cc = (subtypeMap A1).comp e := by
      apply ContinuousMap.ext; intro q; rfl
    rw [hceq, ← CohMap_linear_comp e (subtypeMap A1) R m]
    simpa only [LinearMap.coe_comp] using hbijE.comp hbijA1

end

end Work.StemsB
