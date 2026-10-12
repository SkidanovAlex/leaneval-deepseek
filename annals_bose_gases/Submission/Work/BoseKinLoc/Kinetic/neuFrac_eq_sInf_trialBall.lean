import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.neuFracTrialDefs
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_add_const_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The off-ball estimate

`T(φ,g) ≥ ∫_Λ φ²` as soon as the trial `g` leaves the ball of radius `2R/a²`
(`∫_Λ φ² ≤ R²`).  The estimate is the integrated AM-GM inequality together with the slack
`2R ≥ ‖φ‖_{L²(Λ)}`. -/

/-- **The off-ball estimate.**  If `∫_{Λ}φ² ≤ R²` (`Λ = lamBox ℓ u`, `R > 0`) and the trial
`g` satisfies `(2R/a²)² < ∫_{Λ}g²`, then the trial value `T(φ,g)` is at least the value
`T(φ,0) = ∫_{Λ}φ²` of the zero trial. -/
theorem trialVal_ge_self_of_offBall {ℓ a2 R : ℝ} (ha2 : 0 < a2) (hR : 0 < R)
    (u : EuclideanSpace ℝ (Fin 3)) {φ g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (φ z) ^ 2))
    (hg2 : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)))
    (hRφ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2 ≤ R ^ 2)
    (hoff : (2 * R / a2) ^ 2 < ∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) :
    (∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2)
      ≤ trialVal ℓ a2 u φ g := by
  -- integrability of `φ²` on the box
  have hφ2 := hφ.integrableOn (s := Work.BoseKinLoc.lamBox ℓ u)
  -- the pointwise AM-GM inequality: it is `(2φ − a²g)² ≥ 0`
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      (2 * a2) * (φ z * g z) ≤ 2 * (φ z) ^ 2 + (a2 ^ 2 / 2) * (g z) ^ 2 := by
    intro z
    nlinarith [sq_nonneg (2 * φ z - a2 * g z)]
  -- integrate it (with the `∫ = 0` convention handling the non-integrable case)
  have hbound : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (2 * a2) * (φ z * g z))
      ≤ 2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2)
        + (a2 ^ 2 / 2) * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) := by
    by_cases hInt : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => φ z * g z)
        (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u))
    · have h1 : MeasureTheory.Integrable
          (fun z : EuclideanSpace ℝ (Fin 3) => (2 * a2) * (φ z * g z))
          (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) := hInt.const_mul _
      have h2 : MeasureTheory.Integrable
          (fun z : EuclideanSpace ℝ (Fin 3) => 2 * (φ z) ^ 2 + (a2 ^ 2 / 2) * (g z) ^ 2)
          (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
        (hφ2.const_mul 2).add (hg2.const_mul _)
      have hmono := integral_mono h1 h2 hpt
      have hcomp : (∫ z in Work.BoseKinLoc.lamBox ℓ u,
            (2 * (φ z) ^ 2 + (a2 ^ 2 / 2) * (g z) ^ 2))
          = 2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2)
            + (a2 ^ 2 / 2) * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) := by
        rw [integral_add (hφ2.const_mul 2) (hg2.const_mul _), integral_const_mul,
          integral_const_mul]
      rw [hcomp] at hmono
      exact hmono
    · -- the product is not integrable: the left side is `0` by convention
      have hnot : ¬ MeasureTheory.Integrable
          (fun z : EuclideanSpace ℝ (Fin 3) => (2 * a2) * (φ z * g z))
          (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) := by
        intro hc
        refine hInt ((hc.const_mul (1 / (2 * a2))).congr
          (Filter.Eventually.of_forall fun z => ?_))
        field_simp
      rw [integral_undef hnot]
      have hA : 0 ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2 :=
        integral_nonneg fun z => sq_nonneg _
      have hD : 0 ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2 :=
        integral_nonneg fun z => sq_nonneg _
      nlinarith [hA, hD, sq_nonneg a2]
  -- the kinetic term is nonnegative
  have hK : 0 ≤ ∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
      (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _
  -- the middle term of the trial value is the integral we just bounded
  have hBint : 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, φ z * g z)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (2 * a2) * (φ z * g z) :=
    (integral_const_mul _ _).symm
  -- the slack: `(a²/2)·(2R/a²)² = 2R² ≥ 2∫φ²`
  have hbig : 2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2)
      < (a2 ^ 2 / 2) * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) := by
    have h1 : (a2 ^ 2 / 2) * (2 * R / a2) ^ 2 = 2 * R ^ 2 := by field_simp
    have h2 : (a2 ^ 2 / 2) * (2 * R / a2) ^ 2
        < (a2 ^ 2 / 2) * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) :=
      mul_lt_mul_of_pos_left hoff (by positivity)
    rw [h1] at h2
    nlinarith [h2, hRφ]
  have haK : 0 ≤ a2 * ∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
      (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 := mul_nonneg ha2.le hK
  -- assemble
  simp only [trialVal]
  nlinarith [hbound, hbig, haK, hBint]

/-! ## 2. The infimum over the trial ball

`trialBallSet ⊆ trialSet` gives one inequality, the off-ball estimate the other. -/

theorem neuFrac_eq_sInf_trialBall {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    (u : EuclideanSpace ℝ (Fin 3)) {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφm : MeasureTheory.AEStronglyMeasurable φ MeasureTheory.volume)
    (hφ : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (φ z) ^ 2))
    (hRφ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2 ≤ R ^ 2) :
    Work.BoseKinLoc.neuFrac ℓ a2 u φ
      = sInf (Work.BoseKinLoc.Kinetic.trialBallSet ℓ a2 (2 * R / a2) u φ) := by
  have hM : 0 ≤ 2 * R / a2 := by positivity
  have hbdd_ball : BddBelow (trialBallSet ℓ a2 (2 * R / a2) u φ) :=
    bddBelow_trialBallSet ha2.le u hφ
  have hbdd_set : BddBelow (trialSet ℓ a2 u φ) := bddBelow_trialSet' ha2.le u hφ
  have hne_ball : (trialBallSet ℓ a2 (2 * R / a2) u φ).Nonempty :=
    ⟨_, zero_mem_trialBallSet hM ℓ a2 u φ⟩
  have hne_set : (trialSet ℓ a2 u φ).Nonempty := ⟨_, zero_mem_trialSet ℓ a2 u φ⟩
  -- `neuFrac` is the `sInf` of the full trial set
  rw [neuFrac_eq_sInf_trialSet ℓ a2 u φ]
  refine le_antisymm ?_ ?_
  · -- `sInf trialSet ≤ sInf trialBallSet`: the ball sits inside the set
    refine le_csInf hne_ball fun b hb => ?_
    exact csInf_le hbdd_set (trialBallSet_subset_trialSet ℓ a2 (2 * R / a2) u φ hb)
  · -- `sInf trialBallSet ≤ sInf trialSet`: no outside trial beats the ball
    refine le_csInf hne_set fun c hc => ?_
    rcases hc with ⟨g, hg, hgs, hc⟩
    rw [hc]
    by_cases hball : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) ≤ (2 * R / a2) ^ 2
    · -- the trial is in the ball
      exact csInf_le hbdd_ball ⟨g, hg, hgs, hball, rfl⟩
    · -- the trial is outside the ball: it cannot beat `∫_Λ φ²`
      have hball' : (2 * R / a2) ^ 2 < ∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2 :=
        not_le.mp hball
      have hg2 : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2)
          (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
        Work.BoseKinLoc.NeuFrac.integrableOn_sq_of_contDiff hg hgs u
      have hoff : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2)
          ≤ trialVal ℓ a2 u φ g :=
        trialVal_ge_self_of_offBall ha2 hR u hφ hg2 hRφ hball'
      calc sInf (trialBallSet ℓ a2 (2 * R / a2) u φ)
          ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2 :=
            csInf_le hbdd_ball (zero_mem_trialBallSet hM ℓ a2 u φ)
        _ ≤ trialVal ℓ a2 u φ g := hoff

end Work.BoseKinLoc.Kinetic
