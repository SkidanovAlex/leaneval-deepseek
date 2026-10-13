import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.slicePairIneqFluxFree
import Submission.Work.FTS.EllipticEst.H2W.SlotA.sharpHardyOpen
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_A_integrable
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_integrable_ae

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The `θ`-integrated form of the `(R3)`-with-`κ` slice bound: from the flux inequality for
`∫(σ (v')² + σ v v'')` (in the `wS`-notation of `AngAWeak`) and the four integrability
hypotheses, the paper's constant `κ` appears.  This is the shared tail of
`slice_second_le_flux` and `slice_second_le_flux_small`. -/
private theorem slice_second_of_ibp (v : ℝ → ℝ) (hv : ContDiffOn ℝ 2 v Iθo)
    (hD : MeasureTheory.IntegrableOn
      (fun θ => (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hN : MeasureTheory.IntegrableOn
      (fun θ => (v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Iθo)
    (hG : MeasureTheory.IntegrableOn
      (fun θ => v θ * deriv (deriv v) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hIBP : (∫ θ in Iθo, (Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (deriv v θ) ^ 2
        + Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
            * (v θ * deriv (deriv v) θ)))
      ≤ ∫ θ in Iθo, (2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
            * (v θ) ^ 2
          + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) * (v θ) ^ 2)) :
    (∫ θ in Iθo, v θ * deriv (deriv v) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 2 * Work.Spaces.eta
          * (∫ θ in Iθo, (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * (∫ θ in Iθo, (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hη0 : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have hη1' : 0 < 1 + Work.Spaces.eta := by linarith
  -- the cross term is integrable (AM–GM of the two diagonal squares)
  have hC : MeasureTheory.IntegrableOn
      (fun θ => v θ * deriv v θ * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-1 - Work.Spaces.eta)) Iθo :=
    Work.FTS.EllipticEst.AngAWeak.crossTermIntegrable Work.Spaces.eta hη0 hv hD hN
  -- split the two sides of the flux inequality
  have hLsplit : (∫ θ in Iθo,
        (Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (deriv v θ) ^ 2
          + Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
              * (v θ * deriv (deriv v) θ)))
      = (∫ θ in Iθo, (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + (∫ θ in Iθo, v θ * deriv (deriv v) θ
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    have hcongr : (fun θ => Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (deriv v θ) ^ 2
        + Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
            * (v θ * deriv (deriv v) θ))
        = fun θ => (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + v θ * deriv (deriv v) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      funext θ
      simp only [Work.FTS.EllipticEst.AngAWeak.wS]
      ring
    rw [hcongr, MeasureTheory.integral_add hD hG]
  have hRsplit : (∫ θ in Iθo,
        (2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (v θ) ^ 2
          + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) * (v θ) ^ 2))
      = 2 * Work.Spaces.eta
          * (∫ θ in Iθo, (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
            * (∫ θ in Iθo, (v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) := by
    have hcongr : (fun θ => 2 * Work.Spaces.eta
          * Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (v θ) ^ 2
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) * (v θ) ^ 2)
        = fun θ => 2 * Work.Spaces.eta
            * ((v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
              * ((v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) := by
      funext θ
      simp only [Work.FTS.EllipticEst.AngAWeak.wS]
      ring
    rw [hcongr, MeasureTheory.integral_add (hA.const_mul (2 * Work.Spaces.eta))
      (hN.const_mul (2 * Work.Spaces.eta * (1 + Work.Spaces.eta)))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- the sharp Hardy inequality (with the exponent written as in the statement)
  have hv' : ∀ θ ∈ Iθo, HasDerivAt v (deriv v θ) θ := by
    intro θ hθ
    exact ((hv.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  have hN' : MeasureTheory.IntegrableOn
      (fun θ => (v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta)) Iθo := by
    refine hN.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    rw [show -(2 + Work.Spaces.eta) = -2 - Work.Spaces.eta by ring]
  have hsharp := Work.FTS.EllipticEst.H2W.SlotA.sharpHardyCosWeight_open Work.Spaces.eta hη0 hη1
    v hv' hA hC hN' hD
  set Dint : ℝ := ∫ θ in Iθo, (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    with hDint
  set Aint : ℝ := ∫ θ in Iθo, (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    with hAint
  set Nint : ℝ := ∫ θ in Iθo, (v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
    * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) with hNint
  have hsh : Nint ≤ ((1 + Work.Spaces.eta) ^ 2)⁻¹ * Dint := by
    have heqN : (∫ θ in Iθo, (v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        = ∫ θ in Iθo, (v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-2 - Work.Spaces.eta) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [show -(2 + Work.Spaces.eta) = -2 - Work.Spaces.eta by ring]
    rw [hNint, hDint, heqN]
    simpa only [one_div] using hsharp
  -- the flux inequality, split into the named integrals
  have h1 : Dint + (∫ θ in Iθo, v θ * deriv (deriv v) θ
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 2 * Work.Spaces.eta * Aint
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * Nint := by
    have := hIBP
    rw [hLsplit, hRsplit] at this
    simpa only [hDint, hAint, hNint] using this
  -- the sharp Hardy bound with the effective coefficient
  have h2 : 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * Nint
      ≤ (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * Dint := by
    have hcoef : 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
        = (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (1 + Work.Spaces.eta) ^ 2 := by
      field_simp
      try ring
    have h1' : (1 + Work.Spaces.eta) ^ 2 * Nint ≤ Dint := by
      have hmul := mul_le_mul_of_nonneg_left hsh (pow_nonneg (le_of_lt hη1') 2)
      have hcancel : (1 + Work.Spaces.eta) ^ 2 * ((1 + Work.Spaces.eta) ^ 2)⁻¹ = 1 :=
        mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hη1'))
      calc (1 + Work.Spaces.eta) ^ 2 * Nint
          ≤ (1 + Work.Spaces.eta) ^ 2 * (((1 + Work.Spaces.eta) ^ 2)⁻¹ * Dint) := hmul
        _ = ((1 + Work.Spaces.eta) ^ 2 * ((1 + Work.Spaces.eta) ^ 2)⁻¹) * Dint := by ring
        _ = Dint := by rw [hcancel, one_mul]
    rw [hcoef, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1'
      (div_nonneg (by linarith [hη0]) (le_of_lt hη1'))
  have hcoef2 : ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      = 1 - 2 * Work.Spaces.eta / (1 + Work.Spaces.eta) := by
    field_simp
    try ring
  have hfin : (∫ θ in Iθo, v θ * deriv (deriv v) θ
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 2 * Work.Spaces.eta * Aint
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Dint := by
    rw [hcoef2]
    linarith [h1, h2]
  rw [hAint, hDint] at hfin
  exact hfin

/-- **The `θ`-integration by parts of the flux, with the flux condition only for small `ε`.**

`slice_second_le_flux_small`'s flux input: the same conclusion as the proved
`AngAWeak.fluxIntegralIneq`, but with the hypothesis weakened to
`∃ δ > 0, ∀ ε ∈ (0,δ), fluxG(π/2-ε) - fluxG(ε) ≤ 0`.

Proof: the fundamental theorem of calculus on `[ε_n, π/2-ε_n]` with `ε_n = gapDelta n ↓ 0` gives
`∫_{ε_n}^{π/2-ε_n} fluxGD = fluxG(π/2-ε_n) - fluxG(ε_n) ≤ 0` for all large `n` (the flux
condition holds eventually), and `H2W.tendsto_subinterval_integral` passes to the limit. -/
private theorem slice_flux_ibp_small (v : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v Iθo)
    (hflux : ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) δ,
      Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v (Real.pi / 2 - ε)
        - Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v ε ≤ 0)
    (hGD : MeasureTheory.IntegrableOn
      (Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v) Iθo)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (deriv v θ) ^ 2
        + Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
            * (v θ * deriv (deriv v) θ)) Iθo)
    (hR : MeasureTheory.IntegrableOn
      (fun θ => 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
          * (v θ) ^ 2
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) * (v θ) ^ 2) Iθo) :
    (∫ θ in Iθo, (Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (deriv v θ) ^ 2
        + Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
            * (v θ * deriv (deriv v) θ)))
      ≤ ∫ θ in Iθo, (2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
            * (v θ) ^ 2
          + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) * (v θ) ^ 2) := by
  obtain ⟨δ, hδpos, hδ⟩ := hflux
  have hIθ : MeasureTheory.IntegrableOn
      (Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact hGD.congr_set_ae
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  have htrunc : ∀ᶠ n in Filter.atTop,
      (∫ x in (Work.FTS.EllipticEst.Honest.gapDelta n)..
        (Real.pi / 2 - Work.FTS.EllipticEst.Honest.gapDelta n),
          Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v x) ≤ 0 := by
    filter_upwards [Work.FTS.EllipticEst.Honest.tendsto_gapDelta.eventually_lt_const hδpos]
      with n hn
    have hfluxn : Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v
          (Real.pi / 2 - Work.FTS.EllipticEst.Honest.gapDelta n)
        - Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v
            (Work.FTS.EllipticEst.Honest.gapDelta n) ≤ 0 :=
      hδ _ ⟨Work.FTS.EllipticEst.Honest.gapDelta_pos n, hn⟩
    have hle : Work.FTS.EllipticEst.Honest.gapDelta n
        ≤ Real.pi / 2 - Work.FTS.EllipticEst.Honest.gapDelta n := by
      have := Work.FTS.EllipticEst.Honest.gapDelta_le_half' n
      linarith [Real.pi_gt_three]
    have hftc : (∫ x in (Work.FTS.EllipticEst.Honest.gapDelta n)..
          (Real.pi / 2 - Work.FTS.EllipticEst.Honest.gapDelta n),
            Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v x)
        = Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v
            (Real.pi / 2 - Work.FTS.EllipticEst.Honest.gapDelta n)
          - Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v
              (Work.FTS.EllipticEst.Honest.gapDelta n) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
      · rw [Set.uIcc_of_le hle] at hx
        exact Work.FTS.EllipticEst.AngAWeak.fluxG_hasDerivAt Work.Spaces.eta hv x
          ⟨by linarith [Work.FTS.EllipticEst.Honest.gapDelta_pos n, hx.1],
            by linarith [hx.2, Real.pi_pos, Work.FTS.EllipticEst.Honest.gapDelta_pos n]⟩
      · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr ?_
        exact hIθ.mono_set (fun x hx =>
          ⟨le_of_lt (by linarith [Work.FTS.EllipticEst.Honest.gapDelta_pos n, hx.1]),
            le_of_lt (by linarith [hx.2, Real.pi_pos,
              Work.FTS.EllipticEst.Honest.gapDelta_pos n])⟩)
    rw [hftc]
    exact hfluxn
  have hlimIθ : (∫ x in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v x) ≤ 0 :=
    le_of_tendsto (Work.FTS.EllipticEst.H2W.tendsto_subinterval_integral hIθ) htrunc
  have hlim : (∫ x in Iθo, Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v x) ≤ 0 := by
    have heq : (∫ x in Iθo, Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v x)
        = ∫ x in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v x := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))
    linarith
  set L : ℝ → ℝ := fun θ =>
    Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (deriv v θ) ^ 2
      + Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (v θ * deriv (deriv v) θ)
    with hLdef
  set R : ℝ → ℝ := fun θ =>
    2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (v θ) ^ 2
      + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) * (v θ) ^ 2 with hRdef
  have hEq : (∫ x in Iθo, Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v x)
      = (∫ x in Iθo, L x) - (∫ x in Iθo, R x) := by
    rw [show Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v = fun θ => L θ - R θ from
      funext (fun θ => by
        simp only [hLdef, hRdef, Work.FTS.EllipticEst.AngAWeak.fluxGD,
          Work.FTS.EllipticEst.AngAWeak.wS]
        ring)]
    exact MeasureTheory.integral_sub hL hR
  have hkey : (∫ x in Iθo, L x) ≤ (∫ x in Iθo, R x) := by linarith
  simpa only [hLdef, hRdef] using hkey

/-- **The `κ`-improved second-order slice bound** — the `(R3)`-with-`κ` step of the `I₁` chain
of Step 2 of `prop:H2` of Elgindi, *Annals* **194** (2021), in the *weak* (open-interval) slice
class.

For a slice `v` that is `C²` on the open interval, with the four integrability hypotheses
(`∫σθv²`, `∫σθ(v')²`, `∫σθ₂cos²v²` and `∫σθvv''` finite, all over `(0,π/2)`) and the *flux*
condition

`fluxG(π/2 - ε) - fluxG(ε) ≤ 0`  for `0 < ε < π/4`,  `fluxG = σvv' - (1/2)σ'v²`,

one has  `∫_θ σ v v'' ≤ 2η ∫_θ σ v² - κ ∫_θ σ (v')²`,  with the *sharp* paper constant
`κ = (1-η)/(1+η)` (`η = 99/100`).

Route: `AngAWeak.fluxIntegralIneq` (the `θ`-integration by parts of `(fluxG)' = fluxGD`,
whose truncated boundary term is `≤ 0` by the flux condition) gives
`∫_θ (σ (v')² + σ v v'') ≤ ∫_θ (2ησv² + 2η(1+η)cos²(2θ)σ₂v²)`; rearranging,

`∫_θ σ v v'' ≤ -∫_θ σ (v')² + 2η∫_θ σ v² + 2η(1+η)N`,   `N = ∫_θ cos²(2θ)σ₂ v²`,

and the sharp weighted Hardy inequality `sharpHardyCosWeight_open` gives `N ≤ (1+η)^{-2}∫σθ(v')²`
(with the sharp constant and *no* correction term), so
`2η(1+η)N ≤ (2η/(1+η))∫σθ(v')²` and the coefficient `-1 + 2η/(1+η) = -κ` is exactly the paper's.

The only analytic hypothesis not discharged here is the *flux condition*; it is the single
endpoint input of the weak-class `I₁` bound (the tree's `fluxEndpointBound_aux`). -/
theorem slice_second_le_flux (v : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v Iθo)
    (hflux : ∀ ε ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v (Real.pi / 2 - ε)
        - Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v ε ≤ 0)
    (hD : MeasureTheory.IntegrableOn
      (fun θ => (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hN : MeasureTheory.IntegrableOn
      (fun θ => (v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Iθo)
    (hG : MeasureTheory.IntegrableOn
      (fun θ => v θ * deriv (deriv v) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo) :
    (∫ θ in Iθo, v θ * deriv (deriv v) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 2 * Work.Spaces.eta
          * (∫ θ in Iθo, (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * (∫ θ in Iθo, (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hη0 : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  -- the two sides of the flux inequality are integrable
  have hLint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (deriv v θ) ^ 2
        + Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
            * (v θ * deriv (deriv v) θ)) Iθo := by
    refine (hD.add hG).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    simp only [Work.FTS.EllipticEst.AngAWeak.wS, Pi.add_apply]
    ring_nf
  have hRint : MeasureTheory.IntegrableOn
      (fun θ => 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
          * (v θ) ^ 2
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) * (v θ) ^ 2) Iθo := by
    refine ((hA.const_mul (2 * Work.Spaces.eta)).add (hN.const_mul (2 * Work.Spaces.eta *
      (1 + Work.Spaces.eta)))).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    simp only [Work.FTS.EllipticEst.AngAWeak.wS, Pi.add_apply]
    ring_nf
  have hGDint : MeasureTheory.IntegrableOn
      (Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v) Iθo := by
    refine (hLint.sub hRint).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    simp only [Work.FTS.EllipticEst.AngAWeak.fluxGD, Work.FTS.EllipticEst.AngAWeak.wS,
      Pi.sub_apply]
    ring_nf
  exact slice_second_of_ibp v hv hD hA hN hG
    (Work.FTS.EllipticEst.AngAWeak.fluxIntegralIneq Work.Spaces.eta hη0 v hv hflux
      hGDint hLint hRint)

/-- **The `κ`-improved second-order slice bound, with the flux condition only for *small* `ε`.**

This is the form actually usable in the `θ`-truncation route of the `I₁` bound: for a truncated
slice `U(z,·)·ψ` with `ψ ∈ C_c^∞((0,π/2))` the flux condition holds precisely for
`ε < dist (support ψ) ({0, π/2})`, while the proved `AngAWeak.fluxIntegralIneq` asks for all
`ε ∈ (0,π/4)`.  The truncation argument is therefore repeated here along the sequence
`ε_n = Honest.gapDelta n ↓ 0` (the flux condition holds eventually, and
`H2W.tendsto_subinterval_integral` passes to the limit). -/
theorem slice_second_le_flux_small (v : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v Iθo)
    (hflux : ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) δ,
      Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v (Real.pi / 2 - ε)
        - Work.FTS.EllipticEst.AngAWeak.fluxG Work.Spaces.eta v ε ≤ 0)
    (hD : MeasureTheory.IntegrableOn
      (fun θ => (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo)
    (hN : MeasureTheory.IntegrableOn
      (fun θ => (v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Iθo)
    (hG : MeasureTheory.IntegrableOn
      (fun θ => v θ * deriv (deriv v) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo) :
    (∫ θ in Iθo, v θ * deriv (deriv v) θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 2 * Work.Spaces.eta
          * (∫ θ in Iθo, (v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * (∫ θ in Iθo, (deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hη0 : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  have hLint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ * (deriv v θ) ^ 2
        + Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
            * (v θ * deriv (deriv v) θ)) Iθo := by
    refine (hD.add hG).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    simp only [Work.FTS.EllipticEst.AngAWeak.wS, Pi.add_apply]
    ring_nf
  have hRint : MeasureTheory.IntegrableOn
      (fun θ => 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngAWeak.wS Work.Spaces.eta θ
          * (v θ) ^ 2
        + 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) * (v θ) ^ 2) Iθo := by
    refine ((hA.const_mul (2 * Work.Spaces.eta)).add (hN.const_mul (2 * Work.Spaces.eta *
      (1 + Work.Spaces.eta)))).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    simp only [Work.FTS.EllipticEst.AngAWeak.wS, Pi.add_apply]
    ring_nf
  have hGDint : MeasureTheory.IntegrableOn
      (Work.FTS.EllipticEst.AngAWeak.fluxGD Work.Spaces.eta v) Iθo := by
    refine (hLint.sub hRint).congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ _
    simp only [Work.FTS.EllipticEst.AngAWeak.fluxGD, Work.FTS.EllipticEst.AngAWeak.wS,
      Pi.sub_apply]
    ring_nf
  exact slice_second_of_ibp v hv hD hA hN hG
    (slice_flux_ibp_small v hv hflux hGDint hLint hRint)


end

end Work.FTS.EllipticEst.AeI1Fts
