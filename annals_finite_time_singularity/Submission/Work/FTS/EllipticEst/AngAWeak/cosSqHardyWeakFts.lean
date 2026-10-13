import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.EllipticEst.AngSecond.slice_ftc_zero
import Submission.Work.FTS.EllipticEst.AngAWeakFts.Defs
import Submission.Work.FTS.EllipticEst.AngAWeakFts.fluxDeriv
import Submission.Work.FTS.EllipticEst.AngAWeakFts.fluxIntegrable
import Submission.Work.FTS.EllipticEst.AngAWeakFts.fluxTendsto
import Submission.Work.FTS.EllipticEst.AngAWeakFts.amgmG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The sharp same-weight Hardy inequality with the `cos²(2θ)` factor, in the weak
(open-interval) class** (the constant `1/(1+η)²` is the sharp one for the unconstrained class).
There is no extra integrability hypothesis: `D θ = (deriv f θ)² sin(2θ)^{-η}` is automatically
integrable on `Iθ = [0, π/2]` from `|deriv f θ| ≤ M` and `η < 1`.

Proof (the flux argument, all integrals honest).  The primitive
`Φ θ = f θ² cos(2θ) sin(2θ)^{-(1+η)}` has derivative `2G - 2B - 2(1+η)L` where
`G = f f' cos(2θ) sin(2θ)^{-(1+η)}`, `B = f² sin(2θ)^{-η}`, `L = f² cos²(2θ) sin(2θ)^{-(2+η)}`, and
`|Φ| ≤ M² sin(2θ)^{1-η} → 0` at both endpoints since `η < 1`; hence `∫_{Iθ}(2G-2B-2(1+η)L) = 0`
(`Work.FTS.EllipticEst.AngSecond.slice_ftc_zero`, which needs only `HasDerivAt` on `(0,π/2)`, the
interval-integrability of the derivative, and the two one-sided limits `0`).
The three integrands are dominated by `C sin(2θ)^{-η}` (for `G` and `L` use `|f| ≤ M sin 2θ` and
`|cos| ≤ 1`; for `B` use `sin ≤ 1`), hence integrable on `Iθ` by
`Work.FTS.H2.intervalIntegrable_of_sin_bound` with `p = -η > -1` — the open-interval continuity of
the integrands is lifted from `Ioo` to `Icc` with
`MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc`.  Finally the pointwise AM–GM
`|G| ≤ (ε/2)·L + (1/(2ε))·D` with `ε = 1 + η` gives `(1+η)∫L = ∫G - ∫B ≤ ∫|G| ≤ ((1+η)/2)∫L +
(1/(2(1+η)))∫D`, i.e. `∫L ≤ (1+η)^{-2} ∫D`. -/
theorem cosSqHardyWeakFts (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      (∃ M : ℝ, 0 ≤ M ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M)) →
      (∫ θ in Work.Spaces.Iθ,
          (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
        ≤ 1 / (1 + η) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  intro f hf hbnd
  obtain ⟨M, hM0, hMf, hMd⟩ := hbnd
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- (1) the pointwise derivative of the flux
  have hderiv := Work.FTS.EllipticEst.AngAWeakFts.fluxDeriv η hf
  -- (2) the four integrands are interval integrable
  obtain ⟨hIL, hIB, hIG, hID⟩ :=
    Work.FTS.EllipticEst.AngAWeakFts.fluxIntegrable η hη0 hη1 hf hM0 hMf hMd
  -- (3) the flux vanishes at both endpoints
  obtain ⟨hT0, hTπ⟩ := Work.FTS.EllipticEst.AngAWeakFts.fluxTendsto η hη0 hη1 hM0 hMf
  have hIcomb : IntervalIntegrable
      (fun θ : ℝ => 2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
        - 2 * (1 + η) * hardyFtsL η f θ) volume 0 (Real.pi / 2) :=
    ((hIG.const_mul 2).sub (hIB.const_mul 2)).sub (hIL.const_mul (2 * (1 + η)))
  -- (4) the fundamental theorem of calculus: the flux drops out
  have hftc : (∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
      - 2 * (1 + η) * hardyFtsL η f θ)) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero (hardyFtsFlux η f)
      (fun θ : ℝ => 2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
        - 2 * (1 + η) * hardyFtsL η f θ) hderiv hIcomb hT0 hTπ
  -- (5) integrability over `Iθ` (transport along `Ioc =ᵐ Icc`)
  have hGI : IntegrableOn (hardyFtsG η f) Work.Spaces.Iθ volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hIG).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  have hBI : IntegrableOn (hardyFtsB η f) Work.Spaces.Iθ volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hIB).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  have hLI : IntegrableOn (hardyFtsL η f) Work.Spaces.Iθ volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hIL).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  have hDI : IntegrableOn (hardyFtsD η f) Work.Spaces.Iθ volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hID).congr_set_ae
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  -- (6) linearity of the integral:  `(1+η)∫L = ∫G - ∫B`
  have hlin : (∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
        - 2 * (1 + η) * hardyFtsL η f θ))
      = 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsG η f θ)
        - 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsB η f θ)
        - 2 * (1 + η) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) := by
    have hBA : MeasureTheory.Integrable
        (fun θ : ℝ => 2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (hBI.const_mul 2).add (hLI.const_mul (2 * (1 + η)))
    have hA : (∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ - 2 * hardyFtsB η f θ
          - 2 * (1 + η) * hardyFtsL η f θ))
        = ∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ
            - (2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have hB : (∫ θ in Work.Spaces.Iθ, (2 * hardyFtsG η f θ
            - (2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)))
        = (∫ θ in Work.Spaces.Iθ, 2 * hardyFtsG η f θ)
          - (∫ θ in Work.Spaces.Iθ,
              (2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)) :=
      MeasureTheory.integral_sub (f := fun θ : ℝ => 2 * hardyFtsG η f θ)
        (g := fun θ : ℝ => 2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ)
        (hGI.const_mul 2) hBA
    have hC : (∫ θ in Work.Spaces.Iθ,
          (2 * hardyFtsB η f θ + 2 * (1 + η) * hardyFtsL η f θ))
        = (∫ θ in Work.Spaces.Iθ, 2 * hardyFtsB η f θ)
          + (∫ θ in Work.Spaces.Iθ, 2 * (1 + η) * hardyFtsL η f θ) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => 2 * hardyFtsB η f θ)
        (g := fun θ : ℝ => 2 * (1 + η) * hardyFtsL η f θ)
        (hBI.const_mul 2) (hLI.const_mul (2 * (1 + η)))
    have hD : (∫ θ in Work.Spaces.Iθ, 2 * hardyFtsG η f θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsG η f θ) :=
      MeasureTheory.integral_const_mul 2 (fun θ : ℝ => hardyFtsG η f θ)
    have hE : (∫ θ in Work.Spaces.Iθ, 2 * hardyFtsB η f θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsB η f θ) :=
      MeasureTheory.integral_const_mul 2 (fun θ : ℝ => hardyFtsB η f θ)
    have hF : (∫ θ in Work.Spaces.Iθ, 2 * (1 + η) * hardyFtsL η f θ)
        = 2 * (1 + η) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) :=
      MeasureTheory.integral_const_mul (2 * (1 + η)) (fun θ : ℝ => hardyFtsL η f θ)
    rw [hA, hB, hC, hD, hE, hF]
    ring
  -- (7) the middle term is nonnegative
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, hardyFtsB η f θ :=
    MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => show 0 ≤ (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) from
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hardyFts_sin_nonneg hθ) _)))
  -- (8) the pointwise weighted AM–GM, integrated
  have hGle : (∫ θ in Work.Spaces.Iθ, hardyFtsG η f θ)
      ≤ ((1 + η) / 2) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
        + (1 / (2 * (1 + η))) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) := by
    have hpt : ∀ θ ∈ Work.Spaces.Iθ,
        hardyFtsG η f θ ≤ ((1 + η) / 2) * hardyFtsL η f θ
          + (1 / (2 * (1 + η))) * hardyFtsD η f θ :=
      fun θ hθ => le_trans (le_abs_self _)
        (Work.FTS.EllipticEst.AngAWeakFts.amgmG η hη0 f θ hθ)
    have hR : MeasureTheory.Integrable
        (fun θ : ℝ => ((1 + η) / 2) * hardyFtsL η f θ
          + (1 / (2 * (1 + η))) * hardyFtsD η f θ) (volume.restrict Work.Spaces.Iθ) :=
      (hLI.const_mul ((1 + η) / 2)).add (hDI.const_mul (1 / (2 * (1 + η))))
    have hmono := MeasureTheory.integral_mono_ae hGI hR
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    have h1 : (∫ θ in Work.Spaces.Iθ, (((1 + η) / 2) * hardyFtsL η f θ
          + (1 / (2 * (1 + η))) * hardyFtsD η f θ))
        = (∫ θ in Work.Spaces.Iθ, ((1 + η) / 2) * hardyFtsL η f θ)
          + (∫ θ in Work.Spaces.Iθ, (1 / (2 * (1 + η))) * hardyFtsD η f θ) :=
      MeasureTheory.integral_add (f := fun θ : ℝ => ((1 + η) / 2) * hardyFtsL η f θ)
        (g := fun θ : ℝ => (1 / (2 * (1 + η))) * hardyFtsD η f θ)
        (hLI.const_mul ((1 + η) / 2)) (hDI.const_mul (1 / (2 * (1 + η))))
    have h2 : (∫ θ in Work.Spaces.Iθ, ((1 + η) / 2) * hardyFtsL η f θ)
        = ((1 + η) / 2) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) :=
      MeasureTheory.integral_const_mul ((1 + η) / 2) (fun θ : ℝ => hardyFtsL η f θ)
    have h3 : (∫ θ in Work.Spaces.Iθ, (1 / (2 * (1 + η))) * hardyFtsD η f θ)
        = (1 / (2 * (1 + η))) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) :=
      MeasureTheory.integral_const_mul (1 / (2 * (1 + η))) (fun θ : ℝ => hardyFtsD η f θ)
    rw [h1, h2, h3] at hmono
    exact hmono
  -- (9) the arithmetic:  `(1+η)∫L ≤ ((1+η)/2)∫L + (1/(2(1+η)))∫D`
  have hkey : (1 + η) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
      ≤ ((1 + η) / 2) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
        + (1 / (2 * (1 + η))) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) := by
    have h1 : (1 + η) * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
        = (∫ θ in Work.Spaces.Iθ, hardyFtsG η f θ)
          - (∫ θ in Work.Spaces.Iθ, hardyFtsB η f θ) := by
      linarith [hftc, hlin]
    linarith [h1, hBnn, hGle]
  have hne : ((1 + η) ^ 2) ≠ 0 := by positivity
  have hstep : (1 + η) / 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ)
      ≤ 1 / (2 * (1 + η)) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) := by
    linarith [hkey]
  have h2 : (2 * (1 + η)) * ((1 + η) / 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ))
      ≤ (2 * (1 + η)) * (1 / (2 * (1 + η)) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ)) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have e1 : (2 * (1 + η)) * ((1 + η) / 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ))
      = (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) := by ring
  have e2 : (2 * (1 + η)) * (1 / (2 * (1 + η)) * (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ))
      = (∫ θ in Work.Spaces.Iθ, hardyFtsD η f θ) := by
    rw [one_div, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * (1 + η)) ≠ 0), one_mul]
  rw [e1, e2] at h2
  have e3 : (1 / (1 + η) ^ 2) * ((1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ))
      = (∫ θ in Work.Spaces.Iθ, hardyFtsL η f θ) := by
    rw [← mul_assoc, one_div, inv_mul_cancel₀ hne, one_mul]
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 / (1 + η) ^ 2 by positivity)
  rwa [e3] at h3

end

end Work.FTS.EllipticEst.AngAWeak
