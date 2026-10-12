import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! **The slot-swap identity for the `(n+1)`-body sliding word, *without* a support hypothesis.**

`Work.BSKinetic.tBwordBInd_slotSwap_and_integrable` proves the Fubini/slot decomposition of
`∫_u tBwordBInd (n+1) ℓ d ε c u Φ` under the extra hypothesis `SuppInBox (n+1) ℓ Φ`; that
hypothesis is never used in its proof.  Here we record the two conjuncts that the `B1P`
assembly actually consumes (the identity and the `r`-integrability of each slot summand) for an
arbitrary smooth `Φ` — no support condition.  The proof is the same bookkeeping: the pointwise
slot decomposition `Work.BSKinetic.tBwordBInd_eq_slotSum`, the uniform `u`-bounds of
`Work.BSKinetic.slotWord_bounds` (whose far-vanishing uses only `dlBox = ∅`, never the state),
joint measurability of the slot word, and two applications of Fubini. -/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1P

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem tBwordBInd_slotSwap_nosupp {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.UBBInputs8.tBwordBInd (n + 1) ℓ d ε c u Φ)
        = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
            ∫ u : EuclideanSpace ℝ (Fin 3),
              Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)
    ∧ (∀ i : Fin (n + 1), MeasureTheory.Integrable
        (fun r : Submission.BoseGases.X n =>
          ∫ u : EuclideanSpace ℝ (Fin 3),
            Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r))
        (Work.BSKinetic.boxMu n ℓ)) := by
  classical
  haveI hfin : IsFiniteMeasure (Work.BSKinetic.boxMu n ℓ) :=
    Work.BSKinetic.isFiniteMeasure_boxMu n ℓ hℓ.le
  obtain ⟨K, R, hK0, hR0, hfar, hsmall, hbig⟩ :=
    Work.BSKinetic.slotWord_bounds (ℓ := ℓ) (d := d) (ε := ε) (c := c) hℓ hd n Φ hΦ
  -- joint integrability of the slot word
  have hin : ∀ i : Fin (n + 1), Integrable (Function.uncurry (fun (u : ℝ³) (r : X n) =>
      Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)))
      (volume.prod (Work.BSKinetic.boxMu n ℓ)) := by
    intro i
    refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
      (μ := volume) (ν := Work.BSKinetic.boxMu n ℓ)
      (f := fun (u : ℝ³) (r : X n) =>
        Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r))
      (g := fun _ : X n => ENNReal.ofReal K * volume (Metric.closedBall (0 : ℝ³) R))
      (Work.BSKinetic.SlotSwap.joint_measurable_smallBoxWord1 hℓ hd n Φ hΦ i) ?_ ?_
    · rw [MeasureTheory.lintegral_const, Work.BSKinetic.boxMu, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (MeasureTheory.measure_closedBall_lt_top (x := (0 : ℝ³)) (r := R)).ne)
        (abox_lt_top n ℓ hℓ.le).ne
    · rw [Work.BSKinetic.boxMu, MeasureTheory.ae_restrict_iff' (abox_measurable n ℓ)]
      filter_upwards with r hr
      calc ∫⁻ u, ENNReal.ofReal ‖Work.BSKinetic.smallBoxWord1 ℓ d ε c u
              (Work.BSKinetic.slotState1 i Φ r)‖
          ≤ ∫⁻ u, ENNReal.ofReal K *
              (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ENNReal)) u := by
            apply lintegral_mono; intro u
            show ENNReal.ofReal ‖Work.BSKinetic.smallBoxWord1 ℓ d ε c u
                (Work.BSKinetic.slotState1 i Φ r)‖
                ≤ ENNReal.ofReal K *
                  (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ENNReal)) u
            by_cases hu : u ∈ Metric.closedBall (0 : ℝ³) R
            · rw [Set.indicator_of_mem hu, mul_one]
              exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hsmall i r hr u)
            · rw [Set.indicator_of_notMem hu, mul_zero]
              have hu' : R < ‖u‖ := by
                have h := hu
                rw [Metric.mem_closedBall, dist_zero_right] at h
                exact not_le.mp h
              rw [hfar u hu' i r]
              simp
        _ = ENNReal.ofReal K * volume (Metric.closedBall (0 : ℝ³) R) := by
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            rw [MeasureTheory.lintegral_indicator (Metric.isClosed_closedBall.measurableSet),
              MeasureTheory.setLIntegral_one]
  refine ⟨?_, ?_⟩
  · -- conjunct 1: the Fubini exchange
    rw [show (∫ u : ℝ³, Work.UBBInputs8.tBwordBInd (n + 1) ℓ d ε c u Φ)
        = ∫ u : ℝ³, ∑ i : Fin (n + 1), ∫ r in abox n ℓ,
            Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r) from by
      apply integral_congr_ae
      filter_upwards with u
      exact Work.BSKinetic.tBwordBInd_eq_slotSum hℓ hd n u Φ hΦ]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (n + 1)) (u : ℝ³) => ∫ r in abox n ℓ,
        Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r))
      (fun i _ => ((hin i).integral_prod_left))]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ∫ a : ℝ³, ∫ r, Work.BSKinetic.smallBoxWord1 ℓ d ε c a
          (Work.BSKinetic.slotState1 i Φ r) ∂(Work.BSKinetic.boxMu n ℓ)
        = ∫ r, ∫ u : ℝ³, Work.BSKinetic.smallBoxWord1 ℓ d ε c u
            (Work.BSKinetic.slotState1 i Φ r) ∂volume ∂(Work.BSKinetic.boxMu n ℓ)
    rw [MeasureTheory.integral_integral_swap (μ := volume) (ν := Work.BSKinetic.boxMu n ℓ)
      (hin i)]
  · -- conjunct 2
    intro i
    exact (hin i).integral_prod_right

end Work.BoseFixB1P
