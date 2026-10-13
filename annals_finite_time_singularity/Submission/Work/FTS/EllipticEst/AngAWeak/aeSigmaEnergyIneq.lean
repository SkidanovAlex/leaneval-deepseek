/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AngAWeak/aeSigmaEnergyIneq` — the `σ`-weighted level-`0` energy inequality

The target of this file is the `ρ = w²σ`-weighted energy inequality of Step 1 of `prop:H2` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

in the almost-everywhere weak class `Work.FTS.EllipticEst.H2W.Ae.AeData`, *conditional on* the
slicewise `σ`-coercivity of the angular operator `Lzero1` (the hypothesis `hcoer`):

`∃ C > 0, ∀ α u G, AeData α u G →`
`  ⟦α² z² (∂_zu)² σ⟧ + ⟦(∂_θu)² σ⟧ ≤ C (⟦u² σ⟧ + HkSq α 0 G)`,

where `⟦f⟧ = ∫⁻_z w(z)² ∫⁻_θ ofReal (f z θ)`, `σ = sEta = sin(2θ)^{-η}`, `w z = (1+z)²/z²`.

## Route

Write `ω_n z = w(z)² χ_n(z)` with the cut-off family `Mine.zcutFam` (supported in
`[1/(n+1), 2(n+1)]`, `χ_n → 1` pointwise, with the two uniform logarithmic-derivative bounds
`|z χ_n'| ≤ C₁`, `|z(zχ_n')'| ≤ C₂`), and let `P`, `S`, `R`, `Z`, `L`, `Y` be the slice
functionals `∫_θ σ·(Pu)u`, `∫_θ σ·(Gu)`, `∫_θ σ u²`, `∫_θ σ (z∂_zu)²`, `∫_θ Lzero u · u σ`,
`∫_θ σ (∂_θu)²`.

* The truncated `σ`-weighted radial integration by parts `AeDzParts.puIbpOfChi` turns
  `∫_z ω_n P` into `-α²∫_z ω_n Z + (α²/2)∫(z²ω_n)'' R - (α(5+α)/2)∫(zω_n)' R`, and the two
  transfer terms are bounded by `Λ HkSq α 0 u` with the uniform constant
  `Λ = D₂/32 + 21 D₁/32` (`D₁ = 3 + C₁`, `D₂ = 6 + 4C₁ + (C₂+C₁)`, `omegaW_deriv_bounds`).
* The source pairing is bounded by AM–GM: `∫_z ω_n S ≤ ½(∫_z ω_n G + ∫_z ω_n R)`.
* The hypothesis `hcoer` is applied to every slice `θ ↦ u z θ` (for a.e. `z`), giving both
  `∫_θ (∂_θu)²σ ≤ C₀(∫_θ Lzero u · u σ + K₀ ∫_θ u²σ)` and, dropping the nonnegative left side,
  `∫_θ Lzero u · u σ ≥ -K₀ ∫_θ u²σ`; these are integrated against `ω_n`.
* Combining gives `α² ∫_z ω_n Z + ∫_z ω_n Y ≤ (1+C₀)(1+K₀+Λ) (HkSq α 0 G + HkSq α 0 u)` for
  every `n`; dominated convergence (`χ_n → 1`, `ω_n ≤ w²`) removes the cut-off.
* Finally the `ofReal`/`lintegral` bridges (`H2W.AeU2.ofReal_HkSq_eq_lintegral`, and the same
  computation for `∂_θu` from the slicewise honesty of `(∂_θu)²σ`) turn the real inequality
  into the stated `ℝ≥0∞` inequality.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AngAWeak.aeZWtIBP
import Submission.Work.FTS.EllipticEst.weight_algebra_fts
import Submission.Work.FTS.EllipticEst.AngAWeak.aeLeftTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.AngAWeak.aeSigmaSliceCoercive
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.Prop.Ang2.Sig2
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeSliceFacts
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.Mine.zcutFam
import Submission.Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.H2W.AeU2.ofReal_HkSq_eq_lintegral
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AeStepOneAux.Sig2

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "sg" => Work.FTS.EllipticEst.sEta
local notation "Ith" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

/-! ## The `σ`-weighted angular energy of `∂_θu` -/

/-- `Yslice u z = ∫_θ (∂_θu)(z,θ)² σ θ`, `σ = sin(2θ)^{-η}`. -/
def Yslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Ith, (Work.Spaces.pth u z θ) ^ 2 * sg θ

theorem Yslice_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Yslice u z := by
  rw [Yslice]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ))

theorem Yslice_eq_integral (u : ℝ → ℝ → ℝ) (z : ℝ) :
    Yslice u z = ∫ θ in Ith, (deriv (fun θ' => u z θ')) θ ^ 2 * sg θ := rfl

theorem Rslice_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Rslice u z := by
  rw [Rslice_eq_integral]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ))

theorem Zslice_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Zslice u z := by
  rw [Zslice_eq_integral]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ))

/-! ## The slicewise transfer of the coercivity hypothesis -/

/-- **The slicewise coercivity is inherited by the slices of an `AeData` datum, a.e. in `z`.**
Both the upper bound `∫(∂_θu)²σ ≤ C₀(∫ Lzero u · u σ + K₀ ∫u²σ)` and its consequence
`∫ Lzero u · u σ ≥ -K₀ ∫ u²σ` (drop the nonnegative left-hand side) hold. -/
theorem SliceHcoerAe {C₀ K₀ : ℝ} (hC₀pos : 0 < C₀) (hK₀pos : 0 < K₀)
    (hcoer : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * sg θ) Ith →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv f t) θ) ^ 2 * sg θ) Ith →
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * sg θ) Ith →
      (∫ θ in Ith, (deriv f θ) ^ 2 * sg θ)
        ≤ C₀ * ((∫ θ in Ith, Work.FTS.EllipticEst.Lzero1 f θ * f θ * sg θ)
            + K₀ * (∫ θ in Ith, (f θ) ^ 2 * sg θ)))
    (α : ℝ) (u G : ℝ → ℝ → ℝ) (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Yslice u z ≤ C₀ * (Lslice u z + K₀ * Rslice u z))
    ∧ (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      -(K₀ * Rslice u z) ≤ Lslice u z) := by
  have hL0 := Work.FTS.EllipticEst.AngAWeak.aeLeftTendsto α u G hAe
  have hstep : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Yslice u z ≤ C₀ * (Lslice u z + K₀ * Rslice u z) := by
    filter_upwards [hL0, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hLz hz
    have hRz : Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G hAe z hz
    have hsm : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hAe.smooth hz 2
    obtain ⟨hi1, -, -, -, hi5⟩ :=
      Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G hAe z hz
    have hi3 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2 * sg θ) Ith := by
      refine (Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem (Ψ := u)
        hAe.memAng2 hz).congr_fun (fun θ _ => ?_) measurableSet_Icc
      show Work.Spaces.pthIter 2 u z θ ^ 2 * sg θ
        = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2 * sg θ
      rw [show Work.Spaces.pthIter 2 u z θ
        = deriv (fun t => deriv (fun θ' => u z θ') t) θ from rfl]
    have hkey := hcoer (fun θ => u z θ) hsm hLz hRz hi1 hi3 hi5
    rw [(Yslice_eq_integral u z).symm, ← Rslice_eq_integral u z] at hkey
    exact hkey
  refine ⟨hstep, ?_⟩
  filter_upwards [hstep] with z hz
  have h0 : 0 ≤ C₀ * (Lslice u z + K₀ * Rslice u z) := le_trans (Yslice_nonneg u z) hz
  have h1 : 0 ≤ Lslice u z + K₀ * Rslice u z := by
    by_contra hneg
    have hpos : C₀ * (Lslice u z + K₀ * Rslice u z) < 0 :=
      mul_neg_of_pos_of_neg hC₀pos (not_le.mp hneg)
    linarith [h0]
  linarith

/-! ## The `σ`-slice energy of `∂_θu`: honesty and integrability -/

/-- The `σ`-weighted slice energy of `∂_θu` is dominated by
`10⁴ (∫σ u² + ∫σ (∂_θθu)²)` (`Honest.sliceInterp`). -/
theorem Yslice_le {α : ℝ} {u G : ℝ → ℝ → ℝ} (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z : ℝ, 0 < z →
      Yslice u z ≤ 10000 * (Rslice u z
        + (∫ θ in Ith, (Work.Spaces.pthIter 2 u z θ) ^ 2 * sg θ)) := by
  intro z hz
  have hsm : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hAe.smooth hz 2
  have h0 := (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G hAe z hz).1
  have h2 := Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem (Ψ := u)
    hAe.memAng2 hz
  have h := (Work.FTS.EllipticEst.Honest.sliceInterp (fun θ => u z θ) hsm h0 h2).2
  rw [Yslice, Rslice_eq_integral]
  simpa only [Work.Spaces.pth, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.sEta] using h

/-- The `z`-weighted integral `∫_z w(z)² Yslice u z` is honest, and `Yslice u` is a.e. strongly
measurable. -/
theorem Yslice_integrable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable (Yslice u)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * Yslice u z) Iz := by
  have hU : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hAe
  have hY_aesm : MeasureTheory.AEStronglyMeasurable (Yslice u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hAe.smooth
    have hct : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pth u p.1 p.2) ^ 2 * sg p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth u p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (Work.FTS.EllipticEst.SmoothOpen.forall hSO.pth 0).continuousOn
      have h2 : ContinuousOn (fun p : ℝ × ℝ => sg p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        continuousOn_sEta.comp continuous_snd.continuousOn (fun p hp => hp.2)
      exact (h1.pow 2).mul h2
    have h1 := (Work.Spaces.aesm_of_continuousOn_Qd _ hct).integral_prod_right'
    have h2 : MeasureTheory.AEStronglyMeasurable (Yslice u)
        (MeasureTheory.volume.restrict Iz) :=
      h1.congr (Filter.Eventually.of_forall fun z => rfl)
    exact aesm_restrict_Ioi_of_Iz h2
  refine ⟨hY_aesm, ?_⟩
  have hdom : MeasureTheory.IntegrableOn (fun z => (10000 : ℝ) *
      ((Work.Spaces.w z) ^ 2 * (∫ θ in Ith, (u z θ) ^ 2 * sg θ)
        + (Work.Spaces.w z) ^ 2 * (∫ θ in Ith, (Work.Spaces.pthIter 2 u z θ) ^ 2 * sg θ)))
      Iz :=
    (((integrableOn_phi_mul_slice (α := α) hU).add
      (integrableOn_phi_mul_slice (α := α) hAe.memAng2)).const_mul 10000)
  have hIzeq : MeasureTheory.volume.restrict Iz = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0)).symm
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · refine MeasureTheory.AEStronglyMeasurable.mul
      measurable_w_sq.aestronglyMeasurable ?_
    rw [hIzeq]; exact hY_aesm
  · have hR : Rslice u = fun z => ∫ θ in Ith, (u z θ) ^ 2 * sg θ := by
      funext z; exact Rslice_eq_integral u z
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Yslice_nonneg u z))]
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | h0
    · subst h0
      have hw : (Work.Spaces.w 0) ^ 2 = 0 := by rw [Work.Spaces.w]; norm_num
      calc (Work.Spaces.w 0) ^ 2 * Yslice u 0 = (Work.Spaces.w 0) ^ 2 * Yslice u 0 := rfl
        _ = 0 := by rw [hw, zero_mul]
        _ ≤ (10000 : ℝ) * ((Work.Spaces.w 0) ^ 2 * (∫ θ in Ith, (u 0 θ) ^ 2 * sg θ)
            + (Work.Spaces.w 0) ^ 2 * (∫ θ in Ith, (Work.Spaces.pthIter 2 u 0 θ) ^ 2 * sg θ)) := by
            rw [hw]; simp
    · have hb := mul_le_mul_of_nonneg_left (Yslice_le hAe z h0)
          (sq_nonneg (Work.Spaces.w z))
      rw [hR] at hb
      calc (Work.Spaces.w z) ^ 2 * Yslice u z
          ≤ (Work.Spaces.w z) ^ 2 * (10000 * ((∫ θ in Ith, (u z θ) ^ 2 * sg θ)
              + (∫ θ in Ith, (Work.Spaces.pthIter 2 u z θ) ^ 2 * sg θ))) := hb
        _ = (10000 : ℝ) * ((Work.Spaces.w z) ^ 2 * (∫ θ in Ith, (u z θ) ^ 2 * sg θ)
              + (Work.Spaces.w z) ^ 2 * (∫ θ in Ith,
                  (Work.Spaces.pthIter 2 u z θ) ^ 2 * sg θ)) := by ring

/-! ## The main theorem -/

theorem aeSigmaEnergyIneq
    (hcoer : ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv f t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 f θ * f θ * Work.FTS.EllipticEst.sEta θ)
            + K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
          + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
        ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
            + ENNReal.ofReal (Work.Spaces.HkSq α 0 G)) := by
  obtain ⟨C₀, K₀, hC₀pos, hK₀pos, hcoer₀⟩ := hcoer
  obtain ⟨χ, C₁, C₂, hC₁pos, hC₂pos, hχsm, hχrange, hχleft, hχmid, hχright, hχd1, hχd2,
    hχlim⟩ := Work.FTS.EllipticEst.Mine.zcutFam
  have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
  have hC₂nn : 0 ≤ C₂ := le_of_lt hC₂pos
  set D₁ : ℝ := 3 + C₁ with hD₁def
  set D₂ : ℝ := 6 + 4 * C₁ + (C₂ + C₁) with hD₂def
  have hD₁nn : 0 ≤ D₁ := by rw [hD₁def]; linarith
  have hD₂nn : 0 ≤ D₂ := by rw [hD₂def]; linarith
  set Λ : ℝ := (1 / 32) * D₂ + (21 / 32) * D₁ with hΛdef
  have hΛnn : 0 ≤ Λ := by rw [hΛdef]; positivity
  refine ⟨(1 + C₀) * (1 + K₀ + Λ), by positivity, ?_⟩
  intro α u G hAe
  have hU : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hAe
  have hgrad : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hAe
  obtain ⟨hSliceUp, hSliceLo⟩ := SliceHcoerAe hC₀pos hK₀pos hcoer₀ α u G hAe
  obtain ⟨hY_aesm, hYfull_int⟩ := Yslice_integrable hAe
  have hIzeq : MeasureTheory.volume.restrict Iz = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0)).symm
  have hgsq : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have husq : 0 ≤ Work.Spaces.HkSq α 0 u := Work.Spaces.HkSq_nonneg α 0 u
  have hα2 : α ^ 2 / 2 ≤ 1 / 32 := by
    have h4 : α ≤ 1 / 4 := hAe.hα4
    have hα0 : 0 < α := hAe.hα
    nlinarith
  have hα5 : α * (5 + α) / 2 ≤ 21 / 32 := by
    have h4 : α ≤ 1 / 4 := hAe.hα4
    have hα0 : 0 < α := hAe.hα
    nlinarith
  -- ## the truncated inequality, one cut-off index at a time
  have hcut : ∀ n : ℕ,
      α ^ 2 * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z)
        + (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * χ n z * Yslice u z)
      ≤ ((1 + C₀) * (1 + K₀ + Λ))
          * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
    intro n
    set ω : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * χ n z with hωdef
    have hωm : Measurable ω :=
      measurable_w_sq.mul (hχsm n 2).continuous.measurable
    have hω0 : ∀ z, 0 ≤ ω z := fun z =>
      mul_nonneg (w_sq_nonneg z) (hχrange n z).1
    have hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2 := fun z =>
      mul_le_of_le_one_right (w_sq_nonneg z) (hχrange n z).2
    have hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0) :=
      contDiffOn_w_sq_two.mul (hχsm n 2).contDiffOn
    have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hb : 1 / ((n : ℝ) + 1) < 2 * ((n : ℝ) + 1) := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ h1]; nlinarith [h1]
    -- the two derivative bounds of `χ n`
    have hχ2b : ∀ z, |z ^ 2 * deriv (deriv (χ n)) z| ≤ C₂ + C₁ :=
      chi_second_le (hχsm n 2) (hχd1 n) (hχd2 n)
    have hχb : ∀ z, |χ n z| ≤ 1 := fun z => by
      rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2
    -- the support of `ω`
    have hsupp : ∀ z, z ∉ Set.Icc (1 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1)) → ω z = 0 := by
      intro z hz
      rcases lt_or_ge z (1 / ((n : ℝ) + 1)) with h | h
      · have h1 : χ n z = 0 := hχleft n z (le_of_lt h)
        rw [hωdef]; simp only [h1, mul_zero]
      · have h2 : 2 * ((n : ℝ) + 1) < z := by
          rcases lt_or_ge (2 * ((n : ℝ) + 1)) z with h2 | h2
          · exact h2
          · exact absurd (Set.mem_Icc.mpr ⟨h, h2⟩) hz
        have h1 : χ n z = 0 := hχright n z (le_of_lt h2)
        rw [hωdef]; simp only [h1, mul_zero]
    -- the truncated `σ`-weighted radial integration by parts
    have hA := truncRadialIbpSigma α u hAe.smooth hgrad hAe.memRad2 hU ω hωd ha hb hsupp hω0 hωle
    -- the `w²`-domination data
    have hRphi : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * Rslice u z) Iz :=
      (integrableOn_phi_mul_slice (α := α) hU).congr_fun
        (fun z _ => by simp only [Rslice_eq_integral]) measurableSet_Ici
    have hGphi : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * Gslice G z) Iz :=
      (integrableOn_phi_mul_slice (α := α) hAe.memG).congr_fun
        (fun z _ => by simp only [Gslice_eq_integral]) measurableSet_Ici
    have haesmR : MeasureTheory.AEStronglyMeasurable (Rslice u)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (aesm_slice_sq (α := α) hU).congr
        (Filter.Eventually.of_forall fun z => by simp only [Rslice_eq_integral])
    have haesmG : MeasureTheory.AEStronglyMeasurable (Gslice G)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (aesm_slice_sq (α := α) hAe.memG).congr
        (Filter.Eventually.of_forall fun z => by simp only [Gslice_eq_integral])
    have haesmS : MeasureTheory.AEStronglyMeasurable (Sslice G u)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := aesm_Sslice hAe
    -- AM–GM for the source pairing
    have hSabs : ∀ z, 0 < z →
        |Sslice G u z| ≤ (1 / 2) * (Gslice G z + Rslice u z) := by
      intro z hz
      rw [abs_le]
      constructor
      · have hpt : ∀ θ ∈ Work.Spaces.Iθ, -(1 / 2) *
            (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2) ≤ sg θ * (G z θ * u z θ) := by
          intro θ hθ
          have hσ : 0 ≤ sg θ := Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ
          have h2 : -(1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2) ≤ G z θ * u z θ := by
            nlinarith [sq_nonneg (G z θ + u z θ)]
          calc -(1 / 2) * (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2)
              = sg θ * (-(1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2)) := by ring
            _ ≤ sg θ * (G z θ * u z θ) := mul_le_mul_of_nonneg_left h2 hσ
        have h1 : (∫ θ in Ith, -(1 / 2) *
              (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2)) ≤ Sslice G u z := by
          rw [Sslice]
          refine MeasureTheory.integral_mono_ae
            (((integrableOn_Gslice hAe hz).add (integrableOn_Rslice hAe hz)).const_mul
              (-(1 / 2))) (integrableOn_Sslice hAe hz) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact hpt θ hθ
        have h2 : (∫ θ in Ith, -(1 / 2) *
              (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2))
            = -(1 / 2) * (Gslice G z + Rslice u z) := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_add (integrableOn_Gslice hAe hz)
              (integrableOn_Rslice hAe hz)]
          simp only [Gslice, Rslice]
        calc -(1 / 2 * (Gslice G z + Rslice u z))
            = (∫ θ in Ith, -(1 / 2) *
                (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2)) := by rw [h2]; ring
          _ ≤ Sslice G u z := h1
      · have hpt : ∀ θ ∈ Work.Spaces.Iθ, sg θ * (G z θ * u z θ)
            ≤ (1 / 2) * (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2) := by
          intro θ hθ
          have hσ : 0 ≤ sg θ := Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ
          have h2 : 2 * (G z θ * u z θ) ≤ (G z θ) ^ 2 + (u z θ) ^ 2 := by
            nlinarith [sq_nonneg (G z θ - u z θ)]
          calc sg θ * (G z θ * u z θ)
              = (1 / 2) * (sg θ * (2 * (G z θ * u z θ))) := by ring
            _ ≤ (1 / 2) * (sg θ * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hσ) (by norm_num)
            _ = (1 / 2) * (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2) := by ring
        have h1 : Sslice G u z ≤ (∫ θ in Ith, (1 / 2) *
              (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2)) := by
          rw [Sslice]
          refine MeasureTheory.integral_mono_ae (integrableOn_Sslice hAe hz)
            (((integrableOn_Gslice hAe hz).add (integrableOn_Rslice hAe hz)).const_mul
              (1 / 2)) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact hpt θ hθ
        have h2 : (∫ θ in Ith, (1 / 2) *
              (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2))
            = (1 / 2) * (Gslice G z + Rslice u z) := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_add (integrableOn_Gslice hAe hz)
              (integrableOn_Rslice hAe hz)]
          simp only [Gslice, Rslice]
        calc Sslice G u z
            ≤ (∫ θ in Ith, (1 / 2) *
                (sg θ * (G z θ) ^ 2 + sg θ * (u z θ) ^ 2)) := h1
          _ = (1 / 2) * (Gslice G z + Rslice u z) := h2
    -- integrability of the truncated pairings
    have hRint : MeasureTheory.IntegrableOn (fun z => ω z * Rslice u z) (Set.Ioi 0) :=
      integrableOn_omega_mul hRphi hωm hω0 hωle (fun z => Rslice_nonneg u z) haesmR
    have hGint : MeasureTheory.IntegrableOn (fun z => ω z * Gslice G z) (Set.Ioi 0) :=
      integrableOn_omega_mul hGphi hωm hω0 hωle (fun z => Rslice_nonneg G z) haesmG
    have hYint : MeasureTheory.IntegrableOn (fun z => ω z * Yslice u z) (Set.Ioi 0) :=
      integrableOn_omega_mul hYfull_int hωm hω0 hωle (fun z => Yslice_nonneg u z) hY_aesm
    have hSint : MeasureTheory.IntegrableOn (fun z => ω z * Sslice G u z) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' ((hGint.add hRint).const_mul (1 / 2))
        (hωm.aestronglyMeasurable.mul haesmS) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hω0 z)]
      calc ω z * |Sslice G u z| ≤ ω z * ((1 / 2) * (Gslice G z + Rslice u z)) :=
            mul_le_mul_of_nonneg_left (hSabs z hz) (hω0 z)
        _ = (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by ring
    have hLint : MeasureTheory.IntegrableOn (fun z => ω z * Lslice u z) (Set.Ioi 0) := by
      refine (hA.1.add hSint).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      show ω z * Pslice α u z + ω z * Sslice G u z = ω z * Lslice u z
      rw [Lslice_eq_Pslice_add_Sslice hAe hz]
      ring
    -- `∫ ω P = ∫ ω L - ∫ ω S`
    have hPS : (∫ z in Set.Ioi 0, ω z * Pslice α u z)
        = (∫ z in Set.Ioi 0, ω z * Lslice u z)
          - (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Lslice u z)
          = (∫ z in Set.Ioi 0, ω z * Pslice α u z)
            + (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by
        rw [show (∫ z in Set.Ioi 0, ω z * Lslice u z)
            = ∫ z in Set.Ioi 0, (ω z * Pslice α u z + ω z * Sslice G u z) from by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          show ω z * Lslice u z = ω z * Pslice α u z + ω z * Sslice G u z
          rw [Lslice_eq_Pslice_add_Sslice hAe hz]
          ring]
        exact MeasureTheory.integral_add hA.1 hSint
      linarith [h1]
    -- the two bounds coming from `hcoer`
    have hYω : (∫ z in Set.Ioi 0, ω z * Yslice u z)
        ≤ C₀ * ((∫ z in Set.Ioi 0, ω z * Lslice u z)
            + K₀ * (∫ z in Set.Ioi 0, ω z * Rslice u z)) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Yslice u z)
          ≤ ∫ z in Set.Ioi 0, C₀ * (ω z * Lslice u z + K₀ * (ω z * Rslice u z)) := by
        refine MeasureTheory.integral_mono_ae hYint
          ((hLint.add (hRint.const_mul K₀)).const_mul C₀) ?_
        filter_upwards [hSliceUp, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz _
        calc ω z * Yslice u z ≤ ω z * (C₀ * (Lslice u z + K₀ * Rslice u z)) :=
              mul_le_mul_of_nonneg_left hz (hω0 z)
          _ = C₀ * (ω z * Lslice u z + K₀ * (ω z * Rslice u z)) := by ring
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add hLint (hRint.const_mul K₀),
        MeasureTheory.integral_const_mul] at h1
      exact h1
    have hLω : -(K₀ * (∫ z in Set.Ioi 0, ω z * Rslice u z))
        ≤ ∫ z in Set.Ioi 0, ω z * Lslice u z := by
      have h1 : (∫ z in Set.Ioi 0, (-K₀) * (ω z * Rslice u z))
          ≤ ∫ z in Set.Ioi 0, ω z * Lslice u z := by
        refine MeasureTheory.integral_mono_ae (hRint.const_mul (-K₀)) hLint ?_
        filter_upwards [hSliceLo, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz _
        calc (-K₀) * (ω z * Rslice u z) = ω z * (-(K₀ * Rslice u z)) := by ring
          _ ≤ ω z * Lslice u z := mul_le_mul_of_nonneg_left hz (hω0 z)
      rw [MeasureTheory.integral_const_mul] at h1
      linarith
    have hSle_int : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
        ≤ (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
            + (∫ z in Set.Ioi 0, ω z * Rslice u z)) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
          ≤ ∫ z in Set.Ioi 0, (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by
        refine MeasureTheory.integral_mono_ae hSint ((hGint.add hRint).const_mul (1 / 2)) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        calc ω z * Sslice G u z ≤ ω z * ((1 / 2) * (Gslice G z + Rslice u z)) :=
              mul_le_mul_of_nonneg_left (abs_le.mp (hSabs z hz)).2 (hω0 z)
          _ = (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by ring
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hGint hRint] at h1
      linarith
    -- the coefficient bounds for the two transfer terms
    have hcc1 : ∀ z, 0 < z → |deriv (fun y : ℝ => y * ω y) z|
        ≤ D₁ * (Work.Spaces.w z) ^ 2 := by
      have hfun : (fun y : ℝ => y * ω y)
          = fun y : ℝ => y * ((Work.Spaces.w y) ^ 2 * χ n y) := by
        funext y; rw [hωdef]
      intro z hz
      rw [hfun]
      have h := (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n) hχ2b hχb
        hC₁nn (by linarith)).1 z hz
      rw [hD₁def]; exact h
    have hcc2 : ∀ z, 0 < z →
        |deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z| ≤ D₂ * (Work.Spaces.w z) ^ 2 := by
      have hfun : (fun y : ℝ => y ^ 2 * ω y)
          = fun y : ℝ => y ^ 2 * ((Work.Spaces.w y) ^ 2 * χ n y) := by
        funext y; rw [hωdef]
      intro z hz
      rw [hfun]
      have h := (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n) hχ2b hχb
        hC₁nn (by linarith)).2 z hz
      rw [hD₂def]; exact h
    have hsm1 : MeasureTheory.AEStronglyMeasurable (deriv (fun y : ℝ => y * ω y))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (((contDiffOn_id.mul hωd)).continuousOn_deriv_of_isOpen isOpen_Ioi
        (by norm_num)).aestronglyMeasurable measurableSet_Ioi
    have hsm2 : MeasureTheory.AEStronglyMeasurable
        (deriv (deriv (fun y : ℝ => y ^ 2 * ω y)))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (((((contDiffOn_id.pow 2).mul hωd)).deriv_of_isOpen (m := 1) isOpen_Ioi
        (by norm_num)).continuousOn_deriv_of_isOpen isOpen_Ioi
          (by norm_num)).aestronglyMeasurable measurableSet_Ioi
    have hRid : (∫ z in Iz, (Work.Spaces.w z) ^ 2 * Rslice u z) = Work.Spaces.HkSq α 0 u :=
      (HkSq_zero_eq_Rslice α u).symm
    have hGid : (∫ z in Iz, (Work.Spaces.w z) ^ 2 * Gslice G z) = Work.Spaces.HkSq α 0 G := by
      rw [HkSq_zero_eq_phi_mul α G]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      rw [Gslice_eq_integral]
    have hT1bd : |∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z * Rslice u z|
        ≤ D₁ * Work.Spaces.HkSq α 0 u := by
      have h := (integrableOn_coef_mul_le hRphi hD₁nn hcc1 (fun z => Rslice_nonneg u z) hsm1
        haesmR).2
      rw [hRid] at h
      exact h
    have hT2bd : |∫ z in Set.Ioi 0, deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z|
        ≤ D₂ * Work.Spaces.HkSq α 0 u := by
      have h := (integrableOn_coef_mul_le hRphi hD₂nn hcc2 (fun z => Rslice_nonneg u z) hsm2
        haesmR).2
      rw [hRid] at h
      exact h
    -- the identity in `Z`, `R` form
    have hid : (∫ z in Set.Ioi 0, ω z * Pslice α u z)
        = -α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
          + (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
              deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
          - (α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
              deriv (fun y : ℝ => y * ω y) z * Rslice u z) := by
      have h := hA.2
      simpa only [Rslice, Zslice, Pslice] using h
    have hRωle : (∫ z in Set.Ioi 0, ω z * Rslice u z) ≤ Work.Spaces.HkSq α 0 u := by
      have h := integral_omega_mul_le hRphi hωm hω0 hωle (fun z => Rslice_nonneg u z) haesmR
      rw [hRid] at h
      exact h
    have hGωle : (∫ z in Set.Ioi 0, ω z * Gslice G z) ≤ Work.Spaces.HkSq α 0 G := by
      have h := integral_omega_mul_le hGphi hωm hω0 hωle (fun z => Rslice_nonneg G z) haesmG
      rw [hGid] at h
      exact h
    -- the auxiliary bounds for the two transfer terms
    have hA1 : (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
          deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
        ≤ (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans hT2bd) (by positivity)
    have hA3 : -((α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
          deriv (fun y : ℝ => y * ω y) z * Rslice u z))
        ≤ (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u) := by
      have h2 : -(∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z * Rslice u z)
          ≤ D₁ * Work.Spaces.HkSq α 0 u := (neg_le_abs _).trans hT1bd
      have h3 := mul_le_mul_of_nonneg_left h2 (by nlinarith [hAe.hα] : (0 : ℝ) ≤ α * (5 + α) / 2)
      linarith [h3]
    have hz3 : (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u)
        ≤ ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u := by
      have h := mul_le_mul_of_nonneg_right hα2
        (mul_nonneg hD₂nn (Work.Spaces.HkSq_nonneg α 0 u))
      linarith [h]
    have hz4 : (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u)
        ≤ ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u := by
      have h := mul_le_mul_of_nonneg_right hα5
        (mul_nonneg hD₁nn (Work.Spaces.HkSq_nonneg α 0 u))
      linarith [h]
    have hznn : 0 ≤ ∫ z in Set.Ioi 0, ω z * Zslice u z := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _
      exact mul_nonneg (hω0 z) (Zslice_nonneg u z)
    -- the `α² Z` bound
    have hzbound : α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
        ≤ (1 + K₀ + Λ) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      have hkey : α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
          ≤ K₀ * (∫ z in Set.Ioi 0, ω z * Rslice u z)
            + (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
                + (∫ z in Set.Ioi 0, ω z * Rslice u z))
            + (α ^ 2 / 2) * (D₂ * Work.Spaces.HkSq α 0 u)
            + (α * (5 + α) / 2) * (D₁ * Work.Spaces.HkSq α 0 u) := by
        linarith [hid, hPS, hLω, hSle_int, hA1, hA3]
      have hz1 : K₀ * (∫ z in Set.Ioi 0, ω z * Rslice u z)
          ≤ K₀ * Work.Spaces.HkSq α 0 u :=
        mul_le_mul_of_nonneg_left hRωle (le_of_lt hK₀pos)
      have hz2 : (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
            + (∫ z in Set.Ioi 0, ω z * Rslice u z))
          ≤ (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
        have h3 := add_le_add hGωle hRωle
        linarith [h3]
      have hz5 : K₀ * Work.Spaces.HkSq α 0 u
            + (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)
            + ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u
            + ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u
          ≤ (1 + K₀ + Λ) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
        rw [hΛdef]; nlinarith [hgsq, husq, hK₀pos, hD₁nn, hD₂nn]
      linarith [hkey, hz1, hz2, hz3, hz4, hz5]
    -- the `Y` bound
    have hLK : (∫ z in Set.Ioi 0, ω z * Lslice u z)
          + K₀ * (∫ z in Set.Ioi 0, ω z * Rslice u z)
        ≤ (1 + K₀ + Λ) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Lslice u z)
          = (∫ z in Set.Ioi 0, ω z * Pslice α u z)
            + (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by linarith [hPS]
      have hP : (∫ z in Set.Ioi 0, ω z * Pslice α u z) ≤ Λ * Work.Spaces.HkSq α 0 u := by
        have hb1 : (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
              deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
            ≤ ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u := le_trans hA1 hz3
        have hb2 : -((α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
              deriv (fun y : ℝ => y * ω y) z * Rslice u z))
            ≤ ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u := le_trans hA3 hz4
        have hdist : ((1 / 32) * D₂ + (21 / 32) * D₁) * Work.Spaces.HkSq α 0 u
            = ((1 / 32) * D₂) * Work.Spaces.HkSq α 0 u
              + ((21 / 32) * D₁) * Work.Spaces.HkSq α 0 u := by ring
        have hZ0 : -(α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)) ≤ 0 :=
          neg_nonpos.mpr (mul_nonneg (sq_nonneg α) hznn)
        rw [hΛdef, hdist]
        linarith [hid, hb1, hb2, hZ0]
      have hS2 : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
          ≤ (1 / 2) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
        linarith [hSle_int, hGωle, hRωle]
      have hR2 : K₀ * (∫ z in Set.Ioi 0, ω z * Rslice u z) ≤ K₀ * Work.Spaces.HkSq α 0 u :=
        mul_le_mul_of_nonneg_left hRωle (le_of_lt hK₀pos)
      rw [h1]
      nlinarith [hP, hS2, hR2, hgsq, husq, hΛnn, hK₀pos]
    have hybound : (∫ z in Set.Ioi 0, ω z * Yslice u z)
        ≤ C₀ * ((1 + K₀ + Λ) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) := by
      nlinarith [hYω, hLK, hC₀pos]
    -- assemble
    have hsum : α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
        + (∫ z in Set.Ioi 0, ω z * Yslice u z)
        ≤ (1 + K₀ + Λ) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)
          + C₀ * ((1 + K₀ + Λ) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) :=
      add_le_add hzbound hybound
    have heq : (1 + K₀ + Λ) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)
          + C₀ * ((1 + K₀ + Λ) * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u))
        = ((1 + C₀) * (1 + K₀ + Λ))
          * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by ring
    have hconv : α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
          + (∫ z in Set.Ioi 0, ω z * Yslice u z)
        = α ^ 2 * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z)
          + (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * χ n z * Yslice u z) := by
      rw [hωdef]
    rw [← hconv]
    linarith [hsum, heq]
  -- ## removing the cut-off
  have hlim : α ^ 2 * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Zslice u z)
      + (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Yslice u z)
      ≤ ((1 + C₀) * (1 + K₀ + Λ))
          * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
    have hZphi : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * Zslice u z) Iz :=
      (integrableOn_phi_mul_slice (α := α) hgrad).congr_fun
        (fun z _ => by
          simp only [Zslice_eq_integral, Work.FTS.EllipticEst.H2W.Ae.grad]) measurableSet_Ici
    have hZphi' : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * Zslice u z) (Set.Ioi 0) :=
      hZphi.mono_set Set.Ioi_subset_Ici_self
    have hYphi : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * Yslice u z) (Set.Ioi 0) :=
      hYfull_int.mono_set Set.Ioi_subset_Ici_self
    have haesmZ : MeasureTheory.AEStronglyMeasurable (Zslice u)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (aesm_slice_sq (α := α) hgrad).congr
        (Filter.Eventually.of_forall fun z => by
          simp only [Zslice_eq_integral, Work.FTS.EllipticEst.H2W.Ae.grad])
    have hconvZ : Filter.Tendsto
        (fun n => ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z)
        Filter.atTop (nhds (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Zslice u z)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun z => |(Work.Spaces.w z) ^ 2 * Zslice u z|)
        (F := fun n z => (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z) ?_ hZphi'.abs ?_ ?_
      · intro n
        exact (measurable_w_sq.mul
          (hχsm n 2).continuous.measurable).aestronglyMeasurable.mul haesmZ
      · intro n
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 : |(Work.Spaces.w z) ^ 2| * |χ n z| ≤ |(Work.Spaces.w z) ^ 2| := by
          rw [abs_of_nonneg (w_sq_nonneg z)]
          calc (Work.Spaces.w z) ^ 2 * |χ n z| ≤ (Work.Spaces.w z) ^ 2 * 1 :=
                mul_le_mul_of_nonneg_left
                  (by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2)
                  (w_sq_nonneg z)
            _ = (Work.Spaces.w z) ^ 2 := mul_one _
        calc |(Work.Spaces.w z) ^ 2| * |χ n z| * |Zslice u z|
            ≤ |(Work.Spaces.w z) ^ 2| * |Zslice u z| :=
              mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ = |(Work.Spaces.w z) ^ 2 * Zslice u z| := (abs_mul _ _).symm
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        have h1 : Filter.Tendsto (fun n : ℕ => χ n z) Filter.atTop (nhds 1) := hχlim z hz
        have h2 : (fun n : ℕ => (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z)
            = fun n : ℕ => ((Work.Spaces.w z) ^ 2 * Zslice u z) * χ n z := by
          funext n; ring
        rw [h2]
        simpa using h1.const_mul ((Work.Spaces.w z) ^ 2 * Zslice u z)
    have hconvY : Filter.Tendsto
        (fun n => ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * χ n z * Yslice u z)
        Filter.atTop (nhds (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Yslice u z)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun z => |(Work.Spaces.w z) ^ 2 * Yslice u z|)
        (F := fun n z => (Work.Spaces.w z) ^ 2 * χ n z * Yslice u z) ?_ hYphi.abs ?_ ?_
      · intro n
        exact (measurable_w_sq.mul
          (hχsm n 2).continuous.measurable).aestronglyMeasurable.mul hY_aesm
      · intro n
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 : |(Work.Spaces.w z) ^ 2| * |χ n z| ≤ |(Work.Spaces.w z) ^ 2| := by
          rw [abs_of_nonneg (w_sq_nonneg z)]
          calc (Work.Spaces.w z) ^ 2 * |χ n z| ≤ (Work.Spaces.w z) ^ 2 * 1 :=
                mul_le_mul_of_nonneg_left
                  (by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2)
                  (w_sq_nonneg z)
            _ = (Work.Spaces.w z) ^ 2 := mul_one _
        calc |(Work.Spaces.w z) ^ 2| * |χ n z| * |Yslice u z|
            ≤ |(Work.Spaces.w z) ^ 2| * |Yslice u z| :=
              mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ = |(Work.Spaces.w z) ^ 2 * Yslice u z| := (abs_mul _ _).symm
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        have h1 : Filter.Tendsto (fun n : ℕ => χ n z) Filter.atTop (nhds 1) := hχlim z hz
        have h2 : (fun n : ℕ => (Work.Spaces.w z) ^ 2 * χ n z * Yslice u z)
            = fun n : ℕ => ((Work.Spaces.w z) ^ 2 * Yslice u z) * χ n z := by
          funext n; ring
        rw [h2]
        simpa using h1.const_mul ((Work.Spaces.w z) ^ 2 * Yslice u z)
    exact le_of_tendsto' ((hconvZ.const_mul (α ^ 2)).add hconvY) (fun n => hcut n)
  -- ## the real-level inequality over `Iz`
  have hreal : α ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ)
      + (∫ z in Iz, (Work.Spaces.w z) ^ 2 * Yslice u z)
      ≤ ((1 + C₀) * (1 + K₀ + Λ))
          * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
    have hZeq : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Zslice u z)
        = Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ) := by
      rw [setIntegral_Ioi_eq_Iz, ← HkSq_grad_eq_Zslice α u]
    have hYeq : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Yslice u z)
        = ∫ z in Iz, (Work.Spaces.w z) ^ 2 * Yslice u z := setIntegral_Ioi_eq_Iz _
    rw [hZeq, hYeq] at hlim
    exact hlim
  -- ## the `ℝ≥0∞` bridges
  have hUl : (∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      = ENNReal.ofReal (Work.Spaces.HkSq α 0 u) :=
    (Work.FTS.EllipticEst.H2W.AeU2.ofReal_HkSq_eq_lintegral α u hU).symm
  have hXl : (∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      = ENNReal.ofReal (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ)) := by
    rw [Work.FTS.EllipticEst.H2W.AeU2.ofReal_HkSq_eq_lintegral α
      (fun z θ => z * Work.Spaces.pz u z θ) hgrad]
    refine MeasureTheory.lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z)), mul_assoc]
    congr 1
    rw [← MeasureTheory.lintegral_const_mul']
    · refine MeasureTheory.lintegral_congr fun θ => ?_
      rw [← ENNReal.ofReal_mul (sq_nonneg z)]
      congr 1
      ring
    · exact ENNReal.ofReal_ne_top
  have hYl : (∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      = ENNReal.ofReal (∫ z in Iz, (Work.Spaces.w z) ^ 2 * Yslice u z) := by
    have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
        (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          = ENNReal.ofReal (Yslice u z) := by
      rw [hIzeq]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      have hint := (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G hAe z hz).2.1
      have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          fun θ => (Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
          mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ))
      rw [Yslice]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    calc (∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
        = ∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal (Yslice u z) := by
          refine MeasureTheory.lintegral_congr_ae ?_
          filter_upwards [hpt] with z hz
          rw [hz]
      _ = ∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Yslice u z) := by
          refine MeasureTheory.lintegral_congr fun z => ?_
          exact (ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))).symm
      _ = ENNReal.ofReal (∫ z in Iz, (Work.Spaces.w z) ^ 2 * Yslice u z) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hYfull_int
            (Eventually.of_forall fun z =>
              mul_nonneg (sq_nonneg _) (Yslice_nonneg u z))).symm
  -- ## the final assembly
  have hLHS : ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
        + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      = ENNReal.ofReal (α ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ)
          + (∫ z in Iz, (Work.Spaces.w z) ^ 2 * Yslice u z)) := by
    rw [hXl, hYl]
    rw [← ENNReal.ofReal_mul (sq_nonneg α)]
    rw [← ENNReal.ofReal_add (mul_nonneg (sq_nonneg α) (Work.Spaces.HkSq_nonneg α 0 _))
      (MeasureTheory.integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (Yslice_nonneg u z)))]
  have hRHS : ENNReal.ofReal (((1 + C₀) * (1 + K₀ + Λ))
        * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u))
      = ENNReal.ofReal ((1 + C₀) * (1 + K₀ + Λ))
          * ((∫⁻ z in Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
              + ENNReal.ofReal (Work.Spaces.HkSq α 0 G)) := by
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (Work.Spaces.HkSq_nonneg α 0 G) (Work.Spaces.HkSq_nonneg α 0 u),
      ← hUl]
    congr 1
    exact add_comm _ _
  rw [hLHS, ← hRHS]
  exact ENNReal.ofReal_le_ofReal hreal

end Work.FTS.EllipticEst.AngAWeak
