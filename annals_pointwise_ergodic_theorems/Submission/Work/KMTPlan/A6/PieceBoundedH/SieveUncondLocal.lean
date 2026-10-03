/-
# The sieve-route `uncond` lemmas, re-derived against the current `SieveAssembly`

`Submission/Work/KMTAreas/A7Hi2/sieveRouteUnconditional.lean` (2026-09-30) calls
`Work.A7Hi2.eLpNorm_variationalNorm_lpf_le_sieveMass_of_dilVarRealScale` with `l₁ m₀ hlarge`
appended after `ρ hρ hρ1 r hr p hp`.  `Submission/Work/A7Hi2/SieveAssembly.lean` was changed on
2026-10-01 07:28 to the *stronger* form in which the constant `C` is quantified **outside** the
`∀ l₁ m₀` binder, so its conclusion is now `∃ C, 0 < C ∧ ∀ l₁ m₀, hlarge → ∀ f, …` and those three
extra arguments are no longer accepted: the old file therefore fails to elaborate
(`Function expected at`), and with it every module importing it
(`Work.KMTAreas.A7Hi2.sieveRouteUnconditional`, hence `KMTPlan/A6/PieceBoundedH/sliceGBound` and
`KMTPlan/A6/MdlSliceLowpassG`).

That file is owned by another area; this module is an independent re-derivation of the same two
statements against the *current* `SieveAssembly`, so that the `A6` chain has a buildable route.

The mathematical content is zero: the new signature applies directly.
-/
import Mathlib
import Submission.Work.A7Hi2.SieveAssembly
import Submission.Work.KMTAreas.A7Hi2.dilVarRealScaleFinal

set_option autoImplicit false

namespace Work.KMTPlan.A6.PieceBoundedH

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The sieve bound for the variational norm of the low-pass walk** (re-derived against the
current `Work.A7Hi2.SieveAssembly`; same statement as
`Work.KMTAreas.A7Hi2.eLpNorm_variationalNorm_lpf_le_sieveMass_uncond`, with the constant uniform in
`l₁, m₀`). -/
theorem eLpNorm_variationalNorm_lpf_le_sieveMass_uncondLoc
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      (∀ d ∈ Work.A7Hi2.iwDivs ρ l₁, Work.A7Hi2.sieveCoeff ρ l₁ d ≠ 0 →
        d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) → ∀ f : ℤ → ℂ,
      Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Work.A7Hi2.sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count :=
  Work.A7Hi2.eLpNorm_variationalNorm_lpf_le_sieveMass_of_dilVarRealScale
    Work.KMTAreas.A7Hi2.dilVarRealScale_prop Work.A7Hi2.sieveDecompHyp_holds
    ρ hρ hρ1 r hr p hp

/-- **The values-maximal (`supPart`) sieve bound** (re-derived against the current
`Work.A7Hi2.SieveAssembly`). -/
theorem eLpNorm_supPart_lpf_le_sieveMass_uncondLoc
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      (∀ d ∈ Work.A7Hi2.iwDivs ρ l₁, Work.A7Hi2.sieveCoeff ρ l₁ d ≠ 0 →
        d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) → ∀ f : ℤ → ℂ,
      Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Work.A7Hi2.sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count :=
  Work.A7Hi2.eLpNorm_supPart_lpf_le_sieveMass
    Work.KMTAreas.A7Hi2.dilVarRealScale_prop Work.A7Hi2.sieveDecompHyp_holds
    ρ hρ hρ1 r p hp

/-- **The decimated dilation bound, unconditional** (for completeness of the re-derivation). -/
theorem decimDilBound_uncondLoc : Work.A7Hi2.DecimDilBound :=
  Work.A7Hi2.decimDilBound_of_dilVarRealScale Work.KMTAreas.A7Hi2.dilVarRealScale_prop

end Work.KMTPlan.A6.PieceBoundedH
