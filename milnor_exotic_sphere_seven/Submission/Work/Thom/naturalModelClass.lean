import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Thom.ModelThomA
import Submission.Work.Thom.thomClassTrivialEuclideanA
import Submission.Work.Thom.SuspensionStep
import Submission.Work.Thom.modelSphereBundleStep
import Submission.Work.Thom.CohMap_oneH
import Submission.Work.Cohomology.relComplex_empty_homology_iso
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.step_isModel
import Submission.Work.Thom.step_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

set_option linter.unusedVariables false

open CategoryTheory

noncomputable section

/-! ## The rank-zero model class -/

/-- **Naturality of the rank-zero model class.** -/
theorem Mn_natural_zero (B : Type) [TopologicalSpace B] (W : Set B) :
    (relCohMap (baseIncl B W 0) (Sph W 0) (Sph B 0) (fun _ h => h) ℤ 0).hom (Mn 0 B)
      = Mn 0 W := by
  apply (bijective_relToAbs_sphZero W).1
  have hcomp0 := relCohMap_relToAbs (baseIncl B W 0) (Sph W 0) (Sph B 0) (fun _ h => h) ℤ 0
  have h := LinearMap.congr_fun (congrArg (fun f => f.hom) hcomp0) (Mn 0 B)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, Mn_zero_spec B, Mn_zero_spec W]
  exact CohMap_oneH (baseIncl B W 0)

/-- **The rank-zero model class is a model class**: the cup map with the unit class of
`H^0(B × ℝ⁰, B × S⁰)` is the (bijective) pullback along the projection `B × ℝ⁰ → B`. -/
theorem Mn_isModel_zero (B : Type) [TopologicalSpace B] :
    ∀ k, Function.Bijective (fun x : Coh ℤ k B =>
      (mixedCupC ℤ (Sph B 0) k 0) ((CohMap (projFstA B 0) ℤ k).hom x) (Mn 0 B)) := by
  intro k
  have hsq : ∀ x : B × EuclideanSpace ℝ (Fin 0),
      (⟨fun b : B => (b, (0 : EuclideanSpace ℝ (Fin 0))),
        continuous_id.prodMk continuous_const⟩ : C(B, B × EuclideanSpace ℝ (Fin 0)))
        ((projFstA B 0) x) = x := by
    intro x
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  have hcomp1 : (projFstA B 0).comp (⟨fun b : B => (b, (0 : EuclideanSpace ℝ (Fin 0))),
        continuous_id.prodMk continuous_const⟩ : C(B, B × EuclideanSpace ℝ (Fin 0)))
      = ContinuousMap.id B := by
    ext b; rfl
  have hcomp2 : (⟨fun b : B => (b, (0 : EuclideanSpace ℝ (Fin 0))),
        continuous_id.prodMk continuous_const⟩ : C(B, B × EuclideanSpace ℝ (Fin 0))).comp
        (projFstA B 0) = ContinuousMap.id (B × EuclideanSpace ℝ (Fin 0)) := by
    apply ContinuousMap.ext
    intro x
    exact hsq x
  let HE : ContinuousMap.HomotopyEquiv (B × EuclideanSpace ℝ (Fin 0)) B :=
    ContinuousMap.HomotopyEquiv.mk (projFstA B 0)
      (⟨fun b : B => (b, (0 : EuclideanSpace ℝ (Fin 0))),
        continuous_id.prodMk continuous_const⟩ : C(B, B × EuclideanSpace ℝ (Fin 0)))
      (by rw [hcomp2])
      (by rw [hcomp1])
  have hbij : Function.Bijective ((CohMap (projFstA B 0) ℤ k).hom) :=
    bijective_CohMap_of_homotopyEquiv HE ℤ k
  have hrel : Function.Bijective ((relToAbs ℤ (Sph B 0) (k+0)).hom) := by
    rw [sph_zero_eq_empty]
    exact bijective_relToAbs_empty (k+0)
  have key : ∀ x : Coh ℤ k B,
      (relToAbs ℤ (Sph B 0) (k + 0)).hom
        ((mixedCupC ℤ (Sph B 0) k 0) ((CohMap (projFstA B 0) ℤ k).hom x) (Mn 0 B))
        = (CohMap (projFstA B 0) ℤ k).hom x := by
    intro x
    have h1 := mixedCup_relToAbs (Sph B 0) k 0 ((CohMap (projFstA B 0) ℤ k).hom x) (Mn 0 B)
    rw [h1, Mn_zero_spec B]
    exact Work.Cohomology.cupH'_one_right ℤ
      (TopCat.toSSet.obj (TopCat.of (B × EuclideanSpace ℝ (Fin 0)))) k _
  constructor
  · intro x y hxy
    have h3 : (CohMap (projFstA B 0) ℤ k).hom x = (CohMap (projFstA B 0) ℤ k).hom y := by
      rw [← key x, ← key y]
      exact congrArg (fun w => (relToAbs ℤ (Sph B 0) (k + 0)).hom w) hxy
    exact hbij.1 h3
  · intro z
    obtain ⟨x, hx⟩ := hbij.2 ((relToAbs ℤ (Sph B 0) (k + 0)).hom z)
    refine ⟨x, hrel.1 ?_⟩
    rw [key x, hx]

/-! ## Naturality and the model property of the whole family -/

/-- **The model class is natural in the base.** -/
theorem Mn_natural (n : ℕ) : ∀ (B : Type) [TopologicalSpace B] (W : Set B),
    (relCohMap (baseIncl B W n) (Sph W n) (Sph B n) (fun _ h => h) ℤ n).hom (Mn n B)
      = Mn n W := by
  induction n with
  | zero => intro B _ W; exact Mn_natural_zero B W
  | succ m ih =>
      intro B _ W
      show (relCohMap (baseIncl B W (m+1)) (Sph W (m+1)) (Sph B (m+1)) (fun _ h => h) ℤ (m+1)).hom
          (step B m (Mn m B)) = step W m (Mn m W)
      rw [← step_natural B W m (Mn m B), ih B W]

/-- **Every `Mn n B` is a model class.** -/
theorem Mn_isModel (n : ℕ) : ∀ (B : Type) [TopologicalSpace B] (k : ℕ),
    Function.Bijective (fun x : Coh ℤ k B =>
      (mixedCupC ℤ (Sph B n) k n) ((CohMap (projFstA B n) ℤ k).hom x) (Mn n B)) := by
  induction n with
  | zero => intro B _ k; exact Mn_isModel_zero B k
  | succ m ih => intro B _ k; exact step_isModel B m (Mn m B) (ih B) k

end


/-- **A *natural* model Thom class.**  The model induction of `Submission/Work/Thom/ModelThomA.lean`
produces, for each base `B`, a class of the pair `(B × ℝⁿ, B × S^{n-1})` whose cup map is bijective —
but only as a `Prop`-valued `∃` (`Work.Thom.CleanA.ModelThom`), so the class depends on
`Classical.choose` and is *not* the restriction of the class for a larger base.  What is asked here is
a *choice* `M` of such a class which is **natural in the base**: restricting `M B` along the inclusion
`↥W × ℝⁿ ↪ B × ℝⁿ` (a map of pairs `(↥W × ℝⁿ, ↥W × S^{n-1}) → (B × ℝⁿ, B × S^{n-1})`) gives `M W`.

This is the enabling rung for making the orientation `Work.Thom.IsOrientedOver` provable for a
concrete bundle: with `M` natural, the local data constructed by
`Work.Thom.nonempty_localThom_of_subset_baseSet_of_trivial` restricts correctly, and the only
remaining input is the action of the transition function on the model class (README ADDENDUM 16
§16.5).  Suggested route: build `M` by the same induction as `CleanA.modelThom_base` /
`CleanA.modelThom_step`, but with each step *defined* by its characterising equation
`(relCohMap f …).hom τ' = τ` (the preimage under the bijection `relCohMap f …`), and prove the
naturality by induction from the naturality of `relCohMap` and of the transfers (`Work.Thom.relCohMap_compA`,
`Work.Thom.relCohMap_relToAbs`, and the naturality of `pairδC`/`relToAbs` under restriction).
The preimage under an injective map is natural: if `f : Y → X` restricts along `g : Y' → Y` to
`f' : Y' → X'` (up to the pair conditions), then the preimage of `τ` under `f`, restricted along `g`,
is the preimage of the restriction of `τ` under `f'`. -/
theorem naturalModelClass (n : ℕ) (hn : 1 ≤ n) :
    ∃ M : (B : Type) → [TopologicalSpace B] →
        RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n},
      (∀ (B : Type) [TopologicalSpace B], ∀ k, Function.Bijective (fun x : Coh ℤ k B =>
        (mixedCupC ℤ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n} k n)
          ((CohMap (Work.Thom.projFstA B n) ℤ k).hom x) (M B))) ∧
      (∀ (B : Type) [TopologicalSpace B] (W : Set B),
        (relCohMap (⟨fun p : ↥W × EuclideanSpace ℝ (Fin n) =>
              (((p.1 : ↥W) : B), p.2),
            continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd⟩ :
            C(↥W × EuclideanSpace ℝ (Fin n), B × EuclideanSpace ℝ (Fin n)))
          {p : ↥W × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
          {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n}
          (fun _ hp => hp) ℤ n).hom (M B) = M W) := by
  have _hn : 1 ≤ n := hn
  refine ⟨fun B _ => Mn n B, ?_, ?_⟩
  · intro B _ k
    exact Mn_isModel n B k
  · intro B _ W
    exact Mn_natural n B W

end Work.Thom
