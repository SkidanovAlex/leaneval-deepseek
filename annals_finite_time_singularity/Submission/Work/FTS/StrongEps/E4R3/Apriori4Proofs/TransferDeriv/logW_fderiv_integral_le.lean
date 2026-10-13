import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Flat
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Transfer
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.contDiff_logPull
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.fderiv_logPull_slots
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.norm_fderiv_logPull_sq_le
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open MeasureTheory Set Filter

theorem logW_fderiv_integral_le {w : ℝ → ℝ → ℝ} {g : Work.FTS.Galerkin.Fn}
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hz : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ * (Work.Spaces.Dz g z θ) ^ 2))
            (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad))
    (hth : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ * (Work.Spaces.Dth g z θ) ^ 2))
            (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad)) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2)
      ∧ (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2)
          ≤ 2 * Work.Coercivity.wip w (Work.Spaces.Dz g) (Work.Spaces.Dz g)
            + Work.Coercivity.wip w (Work.Spaces.Dth g) (Work.Spaces.Dth g) := by
  -- The fderiv of the pulled-back profile is continuous (it is `C^1`), hence its norm is
  -- a.e.-measurable; this is what makes the two log-side slot functions measurable.
  have hcontfd : Continuous
      (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.contDiff_logPull hg 1)
      |>.continuous_fderiv (by norm_num)
  -- Measurability of the log pull-back of the two slots, from the slot identities.
  have hFmDz : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g))
      MeasureTheory.volume := by
    have heq : Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g)
        = fun y : ℝ × ℝ => fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
            (ContinuousLinearMap.inl ℝ ℝ ℝ (1 : ℝ)) := by
      funext y
      exact (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.fderiv_logPull_slots
        hg y).1.symm
    rw [heq]
    exact (hcontfd.clm_apply continuous_const).aemeasurable
  have hFmDth : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g))
      MeasureTheory.volume := by
    have heq : Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g)
        = fun y : ℝ × ℝ => 2 * (fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y
            (ContinuousLinearMap.inr ℝ ℝ ℝ (1 : ℝ))) := by
      funext y
      rw [(Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.fderiv_logPull_slots
        hg y).2]
      simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull]
      ring
    rw [heq]
    exact (continuous_const.mul (hcontfd.clm_apply continuous_const)).aemeasurable
  -- The two building blocks: log-side integrability and the value of the plane integrals.
  have hA : Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts
      hw0 hwm hFmDz hz).1
  have hAval : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
      = Work.Coercivity.wip w (Work.Spaces.Dz g) (Work.Spaces.Dz g) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts
      hw0 hwm hFmDz hz).2
  have hB : Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts
      hw0 hwm hFmDth hth).1
  have hBval : (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2)
      = Work.Coercivity.wip w (Work.Spaces.Dth g) (Work.Spaces.Dth g) :=
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogWeightInt.logW_mul_sq_facts
      hw0 hwm hFmDth hth).2
  have hdom : Integrable (fun y : ℝ × ℝ => 2 * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
      + Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2) :=
    (hA.const_mul 2).add hB
  -- The pointwise domination of the integrand by `2 logW (D_z g)² + logW (D_θ g)²`.
  have hle : ∀ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2
      ≤ 2 * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
        + Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2 := by
    intro y
    have hx := mul_le_mul_of_nonneg_left
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts.norm_fderiv_logPull_sq_le
        hg y) (hw0 y)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply] at hx ⊢
    calc Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2
        ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            * (2 * (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2
              + (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2) := hx
      _ = 2 * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            * (Work.Spaces.Dz g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2)
          + Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            * (Work.Spaces.Dth g (Real.exp y.1) (Real.arctan (Real.exp y.2))) ^ 2 := by ring
  -- A.e. strong measurability of the integrand.
  have hmeas : AEStronglyMeasurable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2) MeasureTheory.volume :=
    (hwm.aemeasurable.mul ((hcontfd.norm.pow 2).aemeasurable)).aestronglyMeasurable
  have hmain : Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2) := by
    refine hdom.mono' hmeas ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 y) (sq_nonneg _))]
    exact hle y
  refine ⟨hmain, ?_⟩
  calc ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * ‖fderiv ℝ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) y‖ ^ 2
      ≤ ∫ y : ℝ × ℝ, 2 * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
        + Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2 :=
        integral_mono_ae hmain hdom (Eventually.of_forall hle)
    _ = 2 * (∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dz g) y) ^ 2)
        + ∫ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.Spaces.Dth g) y) ^ 2 := by
        rw [integral_add (hA.const_mul 2) hB, integral_const_mul]
    _ = 2 * Work.Coercivity.wip w (Work.Spaces.Dz g) (Work.Spaces.Dz g)
        + Work.Coercivity.wip w (Work.Spaces.Dth g) (Work.Spaces.Dth g) := by
        rw [hAval, hBval]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
