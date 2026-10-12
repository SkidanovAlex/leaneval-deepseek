import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.MargPiece.integrable_bsW_chiB_sub_holds
import Submission.Work.BoseFixB1S.CubeWindow.marginalCube
import Submission.Work.BoseFixB1S.CubeWindowKinetic
import Submission.Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-- **One slot of the sliding excited count is a.e. strongly measurable in `u`.**

For a fixed slot `i`, the `u`-marginal of `∫_{abox N ℓ} (Q_{B(u),i}Φ)²` is obtained from the
`(u,x)`-joint measurability of FS's box projection `Q_{B(u),i}Φ = 1_{B(u)}(x_i)Φ − P_{B(u),i}Φ`
along the sliding family `B(u) = dlBox ℓ d u` (`Work.BoseFixB1.aemeasurable_boxQInd_sliding`) by
the parametric-integral lemma `AEStronglyMeasurable.integral_prod_right'`.  No integrability,
support or finiteness hypothesis is needed: the box indicator is transported into the product
measure as the measurable set `{q | q.2 ∈ abox N ℓ}` and `boxMass` is allowed to be `0`. -/
lemma aestronglyMeasurable_slotCnPlus {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {N : ℕ} {Φ : X N → ℝ} (hΦ : Continuous Φ) (i : Fin N) :
    MeasureTheory.AEStronglyMeasurable (fun u : E3 =>
      ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) MeasureTheory.volume := by
  classical
  have h0 : AEMeasurable (fun q : E3 × X N =>
      Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
        (Submission.BoseGases.dlBox ℓ d q.1) i Φ q.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    Work.BoseFixB1.aemeasurable_boxQInd_sliding hℓ hd hΦ i
  have hset : MeasurableSet {q : E3 × X N | q.2 ∈ Submission.BoseGases.abox N ℓ} :=
    (Submission.BoseGases.abox_measurable N ℓ).preimage measurable_snd
  have hEq : (fun q : E3 × X N =>
        (Submission.BoseGases.abox N ℓ).indicator
          (fun y : X N =>
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
              (Submission.BoseGases.dlBox ℓ d q.1) i Φ y) ^ 2) q.2)
      = {q : E3 × X N | q.2 ∈ Submission.BoseGases.abox N ℓ}.indicator
          (fun q : E3 × X N =>
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
              (Submission.BoseGases.dlBox ℓ d q.1) i Φ q.2) ^ 2) := by
    funext q
    by_cases h : q.2 ∈ Submission.BoseGases.abox N ℓ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show q ∈
        {q : E3 × X N | q.2 ∈ Submission.BoseGases.abox N ℓ} from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show q ∉
        {q : E3 × X N | q.2 ∈ Submission.BoseGases.abox N ℓ} from h)]
  have hjoint : AEMeasurable (fun q : E3 × X N =>
        (Submission.BoseGases.abox N ℓ).indicator
          (fun y : X N =>
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
              (Submission.BoseGases.dlBox ℓ d q.1) i Φ y) ^ 2) q.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    rw [hEq]
    exact (h0.pow_const 2).indicator hset
  have hint : MeasureTheory.AEStronglyMeasurable (fun u : E3 =>
      ∫ x : X N,
        (Submission.BoseGases.abox N ℓ).indicator
          (fun y : X N =>
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ y) ^ 2) x) MeasureTheory.volume :=
    hjoint.aestronglyMeasurable.integral_prod_right'
  refine hint.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable N ℓ)]

theorem aestronglyMeasurable_cnPlusBoxInd {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) :
    MeasureTheory.AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) Φ) MeasureTheory.volume := by
  classical
  have hG : ∀ i : Fin N, MeasureTheory.AEStronglyMeasurable (fun u : E3 =>
      ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) MeasureTheory.volume :=
    fun i => aestronglyMeasurable_slotCnPlus hℓ hd hΦ i
  have hsum : MeasureTheory.AEStronglyMeasurable (fun u : E3 =>
      ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) MeasureTheory.volume := by
    simpa using (Finset.aestronglyMeasurable_fun_sum (s := Finset.univ)
      (f := fun i : Fin N => fun u : E3 =>
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) (fun i _ => hG i))
  simpa only [Work.UBBInputs8.cnPlusBoxInd] using hsum

end Work.BoseFixB1S
