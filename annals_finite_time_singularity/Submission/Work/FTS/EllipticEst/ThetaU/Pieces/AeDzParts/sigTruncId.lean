import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.momentChainAe
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderAux1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The a.e. slice inequality with the `sec²θ`-slot, in the `AeData` class.**

For every datum `AeData α u G` with `HkMem α 0 u`, for almost every `z > 0`,
`((1-η)/2) Cslice u z ≤ Lslice u z + K Rslice u z`. -/
theorem sliceBarSigmaUpperAe :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 u →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ((1 - Work.Spaces.eta) / 2) * Cslice u z
          ≤ Lslice u z + K * Rslice u z := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.Honest.honSliceSigmaStrong
  refine ⟨K, hKpos, ?_⟩
  intro α u G h _hU
  have hL := Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h
  filter_upwards [hL, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hLz hz
  set f : ℝ → ℝ := fun θ => u z θ with hfdef
  have hf0 : f 0 = 0 := by rw [hfdef]; exact h.dirZero z
  have hfπ : f (Real.pi / 2) = 0 := by rw [hfdef]; exact h.dirPi z
  have hLz' : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa only [hfdef] using hLz
  have hπlim : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := by
    simpa only [hfdef] using
      (Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G h z hz)
  -- the slice is smooth on the open interval
  have hsm_all : ∀ n : ℕ, ContDiffOn ℝ n f (Set.Ioo 0 (Real.pi / 2)) := fun n =>
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz n
  have hsm2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) := hsm_all 2
  -- the `σ`-weighted slice integrabilities supplied by `AeData`
  obtain ⟨hu2, hdu, _h3, _h4, hlz⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G h z hz
  have hdu' : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine hdu.congr_fun (fun θ _ => ?_) measurableSet_Icc
    show (Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [hfdef]
    rfl
  have hu2' : MeasureTheory.IntegrableOn
      (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine hu2.congr_fun (fun θ _ => ?_) measurableSet_Icc
    show (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [hfdef]
  -- `(∂_θθ f)²σ` is integrable
  have hdd : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma (α := α) h.memAng2 hz
    refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
    show (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [hfdef]
    rfl
  -- the one-sided limits of the derivative
  obtain ⟨hlim0, hlimπ⟩ :=
    Work.FTS.EllipticEst.H2W.Ae.slice_deriv_limits hsm2 hdd
  -- the `C¹`-extension of the slice to the closed interval
  obtain ⟨g, hg1, hg0, hgpi, hgeq⟩ :=
    Work.FTS.EllipticEst.Honest.PthCore.contDiffOnOneExtension (f := f)
      (hsm_all 1) hLz' hπlim hlim0 hlimπ
  have hgeqIcc : ∀ θ ∈ Work.Spaces.Iθ, g θ = f θ := by
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, hg0, hf0]
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · rw [h1, hgpi, hfπ]
    · exact (hgeq θ ⟨h0, h1⟩).1
  -- congruence facts between `g` and the fibre, on the open interval
  have hweq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), g θ = f θ ∧ deriv g θ = deriv f θ := by
    intro θ hθ
    exact hgeq θ hθ
  have hLzero_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 g θ = Work.FTS.EllipticEst.Lzero1 f θ := by
    intro θ hθ
    have e1 : deriv (fun t => deriv g t) θ = deriv (fun t => deriv f t) θ := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact (hweq t ht).2
    have e2 : deriv (fun t => Real.tan t * g t) θ
        = deriv (fun t => Real.tan t * f t) θ := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      show Real.tan t * g t = Real.tan t * f t
      rw [(hweq t ht).1]
    simp only [Work.FTS.EllipticEst.Lzero1, e1, e2, (hweq θ hθ).1]
  -- the four integrability hypotheses of the honest lemma for `g`
  have hgdu : MeasureTheory.IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hdu'.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro θ hθ
    show (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [(hweq θ hθ).2]
  have hgddu : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv g) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hdd.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro θ hθ
    have hdderiv : deriv (deriv g) θ = deriv (deriv f) θ := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact (hweq t ht).2
    show (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (deriv g) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [hdderiv]
  have hgu : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (hu2'.mono_set Ioo_subset_Icc_self).congr_fun ?_ measurableSet_Ioo
    intro θ hθ
    show (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [(hweq θ hθ).1]
  have hglz : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 g θ * g θ * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine hlz.congr (Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_)
    intro θ hθ
    show Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ
      = Work.FTS.EllipticEst.Lzero1 g θ * g θ * Work.FTS.EllipticEst.sEta θ
    have h1 : Work.FTS.EllipticEst.Lzero1 f θ = Work.FTS.EllipticEst.Lzero1 g θ :=
      (hLzero_eq θ hθ).symm
    have h2 : f θ = g θ := ((hweq θ hθ).1).symm
    rw [h1, h2]
  -- the honest strong bound for the extension
  have hg2 : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) :=
    hsm2.congr (fun θ hθ => (hweq θ hθ).1)
  have hconc := hK g hg2 hg1 hg0 hgpi hgdu hgddu hgu hglz
  -- transfer back to the fibre
  have hsq : (∫ θ in Work.Spaces.Iθ,
        (g θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = ∫ θ in Work.Spaces.Iθ,
          (f θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp ?_)
    refine Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    show (g θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (f θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [(hweq θ hθ).1]
  have hsqlz : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 g θ * g θ * Work.FTS.EllipticEst.sEta θ)
      = ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp ?_)
    refine Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    show Work.FTS.EllipticEst.Lzero1 g θ * g θ * Work.FTS.EllipticEst.sEta θ
      = Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ
    rw [hLzero_eq θ hθ, (hweq θ hθ).1]
  have hsqg : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc
      ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp ?_)
    refine Work.FTS.EllipticEst.Honest.eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    show (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [(hweq θ hθ).1]
  rw [hsq, hsqlz, hsqg] at hconc
  rw [hfdef] at hconc
  rw [Rslice_eq_integral u z]
  exact hconc

/-! ## Measurability of the slice functionals -/

/-- `Sslice G u` is a.e. strongly measurable (on the open quadrant, `G` agrees with the smooth
`bslOp α u`). -/
theorem aesm_Sslice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable (Sslice G u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hsm
  have hσc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_sEta.comp (continuous_snd.continuousOn) (fun p hp => hp.2)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
      (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hσc.mul (((hbsl.forall 0).continuousOn).mul ((hsm.forall 0).continuousOn))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.bslOp α u z θ * u z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    haesm.congr (ae_restrict_Iz_of_pos (fun z hz => by
      have h1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
            (Work.Elliptic.bslOp α u z θ * u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.sEta θ *
              (Work.Elliptic.bslOp α u z θ * u z θ) :=
        (MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
            (b := Real.pi / 2))).symm
      have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2),
              Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ) :=
        (MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
            (b := Real.pi / 2))).symm
      show (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.bslOp α u z θ * u z θ))
          = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)
      rw [h1, h2]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun θ hθ => by rw [h.eq z hz θ hθ.1 hθ.2])))
  exact aesm_restrict_Ioi_of_Iz h1

/-- `Cslice u` is a.e. strongly measurable. -/
theorem aesm_Cslice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable (Cslice u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (u p.1 p.2 / Real.cos p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (h.smooth 0).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h3 : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)), Real.cos p.2 ≠ 0 := by
      intro p hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)
    have h4 : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2 / Real.cos p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h1.div h2 h3
    have h5 : ContinuousOn (fun p : ℝ × ℝ =>
        Work.FTS.EllipticEst.sEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      continuousOn_sEta.comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact (h4.pow 2).mul h5
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  exact aesm_restrict_Ioi_of_Iz haesm

end Work.FTS.EllipticEst.AeS1
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts.sigTruncId =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Helper lemmas for `sigTruncId`

`sigTruncId` is the `sEta`-weighted truncated energy identity of the almost-everywhere class:
the slice-wise `z`-integration by parts `AngAWeak.sliceIBP` of
`Submission/Work/FTS/EllipticEst/AngAWeak/aeTruncIdent.lean`, integrated in `θ` against the
weight `sEta θ = sin(2θ)^{-η}`, with the joint (product-measure) integrability hypotheses
`hI1`–`hI5` supplying both the Fubini swaps and the a.e.-in-`θ` honesty of the `Lzero`-slice
pairing.

The generic ingredients are separated out below:

* `fubiniWeight` — the weighted Fubini identity in both directions
  `∫_z f z (∫_θ g θ h z θ) = ∫_θ g θ (∫_z f z h z θ)`;
* `Lzero1_slice` — the `θ`-slice of `Lzero1` is `Work.Elliptic.Lzero`;
* `sEta_ne_zero_of_mem_Ioo`, `ae_mem_Ioo_of_mem_Icc` — the structural facts about the
  weight `sEta θ = sin(2θ)^{-η}` used to remove it from the a.e. integrability hypothesis. -/




/-- `sEta` vanishes at the two endpoints of `Iθ`. -/
theorem sEta_zero : Work.FTS.EllipticEst.sEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show (2:ℝ) * 0 = 0 from by ring, Real.sin_zero]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

/-- `sEta` vanishes at the two endpoints of `Iθ`. -/
theorem sEta_pi_div_two : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.sEta,
    show (2:ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_of_mem_Icc : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    θ ∈ Set.Icc (0:ℝ) (Real.pi/2) → θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
  have hsub : {θ : ℝ | ¬ (θ ∈ Set.Icc 0 (Real.pi/2) → θ ∈ Set.Ioo 0 (Real.pi/2))}
      ⊆ ({0, Real.pi/2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq] at hθ
    push Not at hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases eq_or_lt_of_le hθ.1.1 with h | h
    · exact Or.inl h.symm
    · rcases eq_or_lt_of_le hθ.1.2 with h' | h'
      · exact Or.inr h'
      · exact absurd ⟨h, h'⟩ hθ.2
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure ℝ) ({0, Real.pi/2} : Set ℝ) = 0 := by
    rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} from rfl,
      MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)]
    exact MeasureTheory.measure_singleton _
  rw [MeasureTheory.ae_iff]
  exact measure_mono_null hsub hnull


end

end Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts
end
