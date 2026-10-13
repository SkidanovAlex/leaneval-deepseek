import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension
import Submission.Work.EllipticEst.Core.thetaInterpEndpoints
import Submission.Work.FTS.EllipticEst.H2W.AeLeftClean
import Submission.Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeSliceFacts
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Frontier

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `aeSigmaSliceLowerFts` — the slicewise `σ`-coercivity of `Lzero1` in the `AeData` class

For data in the almost-everywhere class `Work.FTS.EllipticEst.H2W.Ae.AeData`, the `θ`-fibre
`f = θ ↦ u z θ` has, for almost every `z > 0`:

* `f` is `C²` on the open interval `(0, π/2)` (`AeData.smooth`) and `f → 0` at `0⁺`
  (`H2W.AeLeftClean.sliceLeftTendstoClean`) and at `(π/2)⁻` (`H2W.Ae.AeSliceRightTendsto`);
* the `σ`-weighted integrands `f² σ`, `(f')² σ`, `(f'')² σ` are honest on `Iθ`, where
  `σ = sin(2θ)^{-η}` (`H2W.AeProof.AeSigma.aeSliceSigmaInt` together with
  `integrableOn_sq_mul_sEtaR_of_HkMem` applied to `AeData.memAng2`).

Hence `Work.EllipticEst.Core.thetaInterpEndpoints` supplies the one-sided limits of `f'`, and
`Honest.PthCore.contDiffOnOneExtension` produces a `C¹`-extension `g` of `f` to `[0, π/2]`
with `g 0 = g (π/2) = 0` and `g = f`, `g' = f'` on the open interval.  The proved slicewise
coercivity `Honest.HonSliceSigmaLower` applied to `g` gives

  `((1-η)/(1+η)) ∫_θ (g')² σ ≤ ∫_θ (Lzero1 g) g σ + K ∫_θ g² σ`,

and dropping the nonnegative left hand side and transferring the integrals back to `f`
(the two functions agree off the null set `{0, π/2}`) yields the claim.
-/

theorem aeSigmaSliceLowerFts : ∃ K : ℝ, 0 < K ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        -K * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.Lzero1 (fun θ => u z θ) θ * u z θ
                * Work.FTS.EllipticEst.sEta θ := by
  have hη0 : 0 ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have hη1 : Work.Spaces.eta < 1 := by norm_num [Work.Spaces.eta]
  obtain ⟨K, hKpos, hK⟩ :=
    Work.FTS.EllipticEst.Honest.HonSliceSigmaLower Work.Spaces.eta hη0 hη1
  refine ⟨K, hKpos, ?_⟩
  intro α u G h
  have hl := Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h
  filter_upwards [hl, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hlz hz
  -- ## the regularity and the a.e. endpoint limits of the fibre
  have hcd : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 2
  have hr : Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) :=
    Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G h z hz
  -- ## the `σ`-weighted integrability of the fibre
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G h z hz
  have hu2 : IntegrableOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := h1
  have hdu : IntegrableOn
      (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pth] using h2
  have hddu : IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have h0 := Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integrableOn_sq_mul_sEtaR_of_HkMem
      (g := Work.Spaces.pthIter 2 u) h.memAng2 hz
    refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.pthIter 2 u z θ
      = deriv (fun t => deriv (fun θ' => u z θ') t) θ from rfl]
  -- ## the one-sided limits of the derivative, and the `C¹`-extension
  obtain ⟨_, _, L₀, L₁, _, _, _, _, hL0, hL1, _, _⟩ :=
    Work.EllipticEst.Core.thetaInterpEndpoints (fun θ => u z θ) hcd hu2 hdu hddu
  obtain ⟨g, hg1, hg0, hgπ, hgEq⟩ :=
    Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension
      (hcd.of_le (by norm_num)) hlz hr ⟨L₀, hL0⟩ ⟨L₁, hL1⟩
  -- ## congruence facts between `g` and the fibre
  have hg2 : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) :=
    hcd.congr (fun θ hθ => (hgEq θ hθ).1)
  have hLzero_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 g θ
        = Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ := by
    intro θ hθ
    have e1 : deriv (fun t => deriv g t) θ
        = deriv (fun t => deriv (fun θ' => u z θ') t) θ := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact (hgEq t ht).2
    have e2 : deriv (fun t => Real.tan t * g t) θ
        = deriv (fun t => Real.tan t * u z t) θ := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      show Real.tan t * g t = Real.tan t * u z t
      rw [(hgEq t ht).1]
    simp only [Work.FTS.EllipticEst.Lzero1, e1, e2, (hgEq θ hθ).1]
  have hdderiv_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv g) θ = deriv (deriv (fun θ' => u z θ')) θ := by
    intro θ hθ
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact (hgEq t ht).2
  -- ## the four integrability hypotheses for `g`
  have hgdu : IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hdu.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro θ hθ
    show (deriv (fun θ' => u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    simp only [(hgEq θ hθ).2]
  have hgddu : IntegrableOn
      (fun θ => (deriv (deriv g) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hddu.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro θ hθ
    show (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      = (deriv (deriv g) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [hdderiv_eq θ hθ]
  have hgu : IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hu2.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro θ hθ
    show (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    simp only [(hgEq θ hθ).1]
  have hglz : IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 g θ * g θ * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine h5.congr (Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_)
    intro θ hθ
    show Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
        * Work.FTS.EllipticEst.sEta θ
      = Work.FTS.EllipticEst.Lzero1 g θ * g θ * Work.FTS.EllipticEst.sEta θ
    rw [← hLzero_eq θ hθ, ← (hgEq θ hθ).1]
  -- ## the coercivity for the extension
  have hconc := hK g hg2 hg1 hg0 hgπ hgdu hgddu hgu hglz
  have hduN : 0 ≤ ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      * (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    refine mul_nonneg (div_nonneg (by linarith) (by linarith)) ?_
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ)
  have hmain : -K * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.Lzero1 g θ * g θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    rw [neg_mul]
    linarith [hconc, hduN]
  have hsEta : ∀ θ : ℝ, (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = Work.FTS.EllipticEst.sEta θ := fun _ => rfl
  -- ## transfer back to the fibre
  have hsq : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp ?_)
    refine Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    show (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [(hgEq θ hθ).1, hsEta θ]
  have hlz : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 g θ * g θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
          * Work.FTS.EllipticEst.sEta θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp ?_)
    refine Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    show Work.FTS.EllipticEst.Lzero1 g θ * g θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ
        * Work.FTS.EllipticEst.sEta θ
    rw [hLzero_eq θ hθ, (hgEq θ hθ).1, hsEta θ]
  rw [hsq, hlz] at hmain
  exact hmain

end Work.FTS.EllipticEst.Frontier
