import Mathlib
import Submission.Work.Thom.Orientation.ReflSections
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Cohomology.h0Evaluation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Thom
open Work.Thom.Orientation

noncomputable section

/-!
# The rank-one model class is a connecting homomorphism on the sphere bundle

For the **trivial real line bundle** over a space `Y` the sphere bundle of rank one is
`Sph Y 1 = Y × S⁰ ⊆ Y × ℝ¹`, and the rank-one model class `Work.Thom.Mn 1 Y` is a class of the
pair `(Y × ℝ¹, Sph Y 1)`.

The theorem `Work.Whitney.Mn_one_eq_pairDelta` produces an explicit class
`w ∈ H⁰(Sph Y 1; ℤ)` with

* `σ₊^* w = 1` — the restriction to the *positive* constant section `y ↦ (y, +1)` is the unit class
  of `H⁰(Y;ℤ)`;
* `σ₋^* w = 0` — the restriction to the *negative* constant section `y ↦ (y, -1)` vanishes;
* `δ w = Mn 1 Y` — the connecting homomorphism `δ : H⁰(Sph Y 1) → H¹(Y × ℝ¹, Sph Y 1)` of the pair
  sends `w` to the Thom class of the trivial line bundle.

So `w` is the class that is `1` on the positive end of every fibre and `0` on the negative end, and
`Mn 1` is its transgression: the rank-one Thom class is the transgression of the *difference of the
two ends* of the line bundle (this is the "orientation" input for the rank-one model class).

## The three inequalities are proved as follows

* The *witness* is the class appearing in the definition of `Work.Thom.step`:
  `w = (Φ⁻¹)^*(relToAbs (stepSph Y 0 (Mn 0 Y)))`, where `Φ : Y × S⁰ ≃ₜ ↥(Sph Y 1)` is the canonical
  homeomorphism `prodSubsetHomeoA`.  The third conjunct is then *definitional*: `Mn 1 Y` unfolds to
  `step Y 0 (Mn 0 Y) = δ w`.
* The *negative section* factors through the subset `SphB Y 0 = Y × {-1}` on which the relative
  class `stepSph Y 0 (Mn 0 Y)` restricts to zero (the composite `relToAbs ≫ (subtype)^*` is zero):
  hence `σ₋^* w = 0`.  (Here `mLower 0 = {-1}`, so the "lower band" is exactly the negative end.)
* The *positive section* factors through the **cap map** `capMapPairSph Y 0`, because
  `capMap 0 0 = +1` (`mBall 0` is a point and `capMap` is the graph of the upper hemisphere).
  The cap equation `stepSph_spec` (`cap^* (stepSph Y 0 (Mn 0 Y)) = stepDisc Y 0 (Mn 0 Y)`),
  `stepDisc = discFullMap^*` and `Mn 0 Y` being the unit class (`Mn_zero_spec`) together give
  `cap^*(relToAbs (stepSph Y 0 (Mn 0 Y))) = 1`, and pullback fixes the unit class.
-/

/-- The canonical homeomorphism `Y × S⁰ ≅ ↥(Sph Y 1)` of `Work.Thom.prodSubsetHomeoA`,
viewed as a continuous map in the direction `Sph Y 1 → Y × S⁰`. -/
abbrev sphEsymm (Y : Type) [TopologicalSpace Y] : C(↥(Sph Y 1), Y × MSph 1) :=
  ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin 1)) (mSph 1)).symm : C(↥(Sph Y 1), Y × MSph 1))

/-- The section `y ↦ (y, 0)` of `Y × D⁰` (`D⁰` is a point). -/
noncomputable def zeroSect (Y : Type) [TopologicalSpace Y] : C(Y, Y × MBall 0) :=
  ⟨fun y => (y, ⟨0, by simp [mBall]⟩), continuous_id.prodMk continuous_const⟩

/-- The cap map at rank `0` sends the (unique) point of `D⁰` to `+1 ∈ S⁰ ⊆ ℝ¹`. -/
theorem capMap_zero_zero : capMap 0 (0 : EuclideanSpace ℝ (Fin 0)) = sphPlus := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  simp [capMap_ofLp, sphPlus, Work.Cohomology.s0N, Fin.snoc]

/-- `-1 ∈ ℝ¹` lies in the lower band `mLower 0` (which is the single point `-1`). -/
theorem sphMinus_mem_mLower_zero : sphMinus ∈ mLower 0 := by
  refine ⟨sphMinus_mem, ?_⟩
  show (sphMinus : EuclideanSpace ℝ (Fin 1)).ofLp (Fin.last 0) ≤ (1:ℝ)/2
  simp only [sphMinus, Work.Cohomology.s0S, WithLp.ofLp_toLp]
  norm_num

/-- The section of `SphB Y 0 ⊆ Y × S⁰` over the point `-1` of the fibre.  Note
`SphB Y 0 = {p : Y × MSph 1 | p.2.1 ∈ mLower 0}` and `mLower 0 = {-1}`. -/
noncomputable def negSect (Y : Type) [TopologicalSpace Y] : C(Y, ↥(SphB Y 0)) :=
  ⟨fun y => ⟨(y, ⟨sphMinus, sphMinus_mem⟩), sphMinus_mem_mLower_zero⟩,
    Continuous.subtype_mk (continuous_id.prodMk continuous_const) _⟩

/-- **The positive section is the cap map at rank `0`**: `σ₊ = capMapPairSph Y 0 ∘ (y ↦ (y,0))`. -/
theorem sphEsymm_comp_sigPos (Y : Type) [TopologicalSpace Y] :
    (sphEsymm Y).comp (sigPos (Y := Y)) = (capMapPairSph Y 0).comp (zeroSect Y) := by
  apply ContinuousMap.ext
  intro y
  simp only [ContinuousMap.comp_apply]
  rw [show (sphEsymm Y) (sigPos (Y := Y) y)
      = ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin 1)) (mSph 1)).symm (sigPos (Y := Y) y))
      from rfl]
  rw [prodSubsetHomeoA_symm_apply]
  simp only [zeroSect, capMapPairSph, ContinuousMap.coe_mk, sigPos_apply]
  congr 1
  apply Subtype.ext
  exact capMap_zero_zero.symm

/-- **The negative section lands in the lower band**: `σ₋ = (SphB Y 0 ↪ Y × S⁰) ∘ negSect`. -/
theorem sphEsymm_comp_sigNeg (Y : Type) [TopologicalSpace Y] :
    (sphEsymm Y).comp (sigNeg (Y := Y)) = (subtypeMap (SphB Y 0)).comp (negSect Y) := by
  apply ContinuousMap.ext
  intro y
  simp only [ContinuousMap.comp_apply]
  rw [show (sphEsymm Y) (sigNeg (Y := Y) y)
      = ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin 1)) (mSph 1)).symm (sigNeg (Y := Y) y))
      from rfl]
  rw [prodSubsetHomeoA_symm_apply]
  simp only [negSect, subtypeMap, ContinuousMap.coe_mk, sigNeg_apply]

/-- A class of `H^n(X,A;ℤ)` gives zero in `H^n(A;ℤ)`: the composite of the forgetful map with the
restriction to the subspace is zero (`Work.Thom.relToAbs_comp_CohMap_subtype`). -/
theorem CohMap_subtypeMap_relToAbs {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (x : RelCoh ℤ n X A) :
    (CohMap (subtypeMap A) ℤ n).hom ((relToAbs ℤ A n).hom x) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (relToAbs_comp_CohMap_subtype ℤ A n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact LinearMap.congr_fun h x

theorem Mn_one_eq_pairDelta (Y : Type) [TopologicalSpace Y] :
    ∃ w : Work.Thom.Coh ℤ 0 ↥(Work.Thom.Sph Y 1),
      (Work.Thom.CohMap (Work.Thom.Orientation.sigPos (Y := Y)) ℤ 0).hom w
          = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Y)) ∧
      (Work.Thom.CohMap (Work.Thom.Orientation.sigNeg (Y := Y)) ℤ 0).hom w = 0 ∧
      (Work.Thom.pairδC (Work.Thom.Sph Y 1) 0).hom w = Work.Thom.Mn 1 Y := by
  classical
  -- the witness: the class of `Work.Thom.step`, i.e. `Mn 1 Y` is its connecting homomorphism
  set w : Work.Thom.Coh ℤ 0 ↥(Work.Thom.Sph Y 1) :=
    (CohMap (sphEsymm Y) ℤ 0).hom
      ((relToAbs ℤ (SphB Y 0) 0).hom (stepSph Y 0 (Mn 0 Y))) with hwdef
  -- the cap equation: the cap map identifies the transferred class with the rank-zero unit class
  have hcap : (CohMap (capMapPairSph Y 0) ℤ 0).hom
      ((relToAbs ℤ (SphB Y 0) 0).hom (stepSph Y 0 (Mn 0 Y)))
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (Y × MBall 0))) := by
    rw [← relCohMap_relToAbs_apply (capMapPairSph Y 0) (DiscB Y 0) (SphB Y 0)
      (CleanA.capMapPairSph_mem_mLower 0) ℤ 0 (stepSph Y 0 (Mn 0 Y))]
    rw [stepSph_spec Y 0 (Mn 0 Y)]
    rw [show stepDisc Y 0 (Mn 0 Y) = (relCohMap (CleanA.discFullMap Y 0) (DiscB Y 0) (Sph Y 0)
      (CleanA.discFullMap_mem Y 0) ℤ 0).hom (Mn 0 Y) from rfl]
    rw [relCohMap_relToAbs_apply (CleanA.discFullMap Y 0) (DiscB Y 0) (Sph Y 0)
      (CleanA.discFullMap_mem Y 0) ℤ 0 (Mn 0 Y)]
    rw [Mn_zero_spec Y]
    rw [show oneSphZero Y = Work.Cohomology.oneH ℤ
      (TopCat.toSSet.obj (TopCat.of (Y × EuclideanSpace ℝ (Fin 0)))) from rfl]
    rw [CohMap_oneH (CleanA.discFullMap Y 0)]
  refine ⟨w, ?_, ?_, ?_⟩
  · -- the restriction to the positive section is the unit class
    rw [hwdef]
    rw [CohMap_comp_apply (sigPos (Y := Y)) (sphEsymm Y) ℤ 0
      ((relToAbs ℤ (SphB Y 0) 0).hom (stepSph Y 0 (Mn 0 Y)))]
    rw [sphEsymm_comp_sigPos Y]
    rw [← CohMap_comp_apply (zeroSect Y) (capMapPairSph Y 0) ℤ 0
      ((relToAbs ℤ (SphB Y 0) 0).hom (stepSph Y 0 (Mn 0 Y)))]
    rw [hcap]
    exact CohMap_oneH (zeroSect Y)
  · -- the restriction to the negative section vanishes
    rw [hwdef]
    rw [CohMap_comp_apply (sigNeg (Y := Y)) (sphEsymm Y) ℤ 0
      ((relToAbs ℤ (SphB Y 0) 0).hom (stepSph Y 0 (Mn 0 Y)))]
    rw [sphEsymm_comp_sigNeg Y]
    rw [← CohMap_comp_apply (negSect Y) (subtypeMap (SphB Y 0)) ℤ 0
      ((relToAbs ℤ (SphB Y 0) 0).hom (stepSph Y 0 (Mn 0 Y)))]
    rw [CohMap_subtypeMap_relToAbs (SphB Y 0) 0 (stepSph Y 0 (Mn 0 Y))]
    simp
  · -- the connecting homomorphism of the witness is the rank-one model class, by definition
    rw [hwdef]
    rfl

end

end Work.Whitney
