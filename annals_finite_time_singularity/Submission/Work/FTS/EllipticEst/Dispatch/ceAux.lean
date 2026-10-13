import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools
import Submission.Work.FTS.EllipticEst.Dispatch.weightAlgChi
import Submission.Work.FTS.EllipticEst.Dispatch.AeCutGDefs
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceSelfForm
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.AeS1.aeSliceConds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The per-slice coercivity of `Lzero` on the fibres of an `AeData` datum, a.e. in `z`. -/
theorem ceCoercive {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hL0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hLπ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ)
          + 6 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
  have key : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ)
          + 6 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
    filter_upwards [hL0, hLπ, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hl0 hlp hz
    have hcz : ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.H2W.AeProof.continuousOn_Icc_of_tendsto
        (by linarith [Real.pi_pos])
        (Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 1).continuousOn
        (by simpa only [h.dirZero z] using hl0) (by simpa only [h.dirPi z] using hlp)
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz n
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
      have h1 := Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma (α := α) h.memAng2 hz
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using h1
    have hsf := Work.FTS.EllipticEst.H2W.AeProof.AeSliceSelfForm u z hsm hcz (h.dirZero z)
      (h.dirPi z) hint
    have hpos : 0 ≤ (1 / 2 : ℝ) * (∫ θ in Work.Spaces.Iθ, (u z θ / Real.cos θ) ^ 2) :=
      mul_nonneg (by norm_num) (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
    have hrewrite : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => u z θ') θ) ^ 2 := rfl
    rw [hrewrite, hsf]
    linarith
  rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact key

/-- The pointwise weight bounds of the truncated `w²`-energy inequality. -/
theorem ceWeightBound (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (hφnn : ∀ z : ℝ, 0 ≤ φ z) :
    (∀ z : ℝ, 0 < z →
        deriv (deriv (fun z' : ℝ => φ z' * (Work.Spaces.w z') ^ 2 * z' ^ 2)) z
          ≤ 6 * (φ z * (Work.Spaces.w z) ^ 2)
            + 2 * |deriv φ z| * |deriv (fun z' : ℝ => z' ^ 2 * (Work.Spaces.w z') ^ 2) z|
            + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      ∧ (∀ z : ℝ, 0 < z →
        - deriv (fun z' : ℝ => φ z' * (Work.Spaces.w z') ^ 2 * z') z
          ≤ 3 * (φ z * (Work.Spaces.w z) ^ 2)
            + |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)) := by
  obtain ⟨h1, h2⟩ := weightAlgChi φ hφ hφnn
  constructor
  · intro z hz
    have h := h1 z hz
    have hfun : (fun y : ℝ => y ^ 2 * Wcut φ y)
        = fun y : ℝ => φ y * (Work.Spaces.w y) ^ 2 * y ^ 2 := by
      funext y; rw [Wcut]; ring
    rw [hfun] at h
    have hW : Wcut φ z = φ z * (Work.Spaces.w z) ^ 2 := rfl
    rw [hW] at h
    have hF2 : AeCut.F2g φ z
        = 2 * |deriv φ z| * |deriv (fun z' : ℝ => z' ^ 2 * (Work.Spaces.w z') ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) := rfl
    rw [hF2] at h
    linarith [h]
  · intro z hz
    have h := h2 z hz
    have hfun : (fun y : ℝ => y * Wcut φ y)
        = fun y : ℝ => φ y * (Work.Spaces.w y) ^ 2 * y := by
      funext y; rw [Wcut]; ring
    rw [hfun] at h
    have hW : Wcut φ z = φ z * (Work.Spaces.w z) ^ 2 := rfl
    rw [hW] at h
    have hF1 : AeCut.F1g φ z = |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) := rfl
    rw [hF1] at h
    linarith

end Work.FTS.EllipticEst.Dispatch
