import Mathlib
import Submission.Work.KMTPlan.A6.Decim.Defs
import Submission.Work.KMTPlan.A6.iwKernelDecaySharp

namespace Work.KMTAreas.A7Hi

open MeasureTheory

/-!
# `ℓ¹`-summability of the kernel of the Ionescu--Wainger symbol of the dyadic circle bump

The dyadic bump `Work.KMTPlan.A6.Decim.bump L = periodize (etaCut kmtEta (-(L : ℤ)))` is the
periodisation of the KMT cutoff `η_{≤-L}`, a smooth compactly supported function on `ℝ`.  For any
finite set `A` of circle frequencies, the Fourier-coefficient sequence of the Ionescu--Wainger
symbol `iwSymbolSet A (bump L)` is therefore absolutely summable:

  `Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet A (bump L)) j‖)`.

The proof is the quadratic decay `Work.KMTPlan.A6.iwKernelDecaySharp` — the Poisson-summation
identity `iwKernel = 𝓕 (sum of translates)` combined with the sharp `C²` Fourier decay
`fourierDecaySharp` — which gives the pointwise bound

  `‖iwKernel (iwSymbolSet A (periodize F)) j‖ ≤ 4 · (card A · max ‖F‖₁ ‖F´´‖₁) · ‖kmtKernWeight j‖`

for `F = etaCut kmtEta (-(L : ℤ))` (`ContDiff` and `HasCompactSupport` from `A7/Basic.lean`), and
`kmtKernWeight j = (1 + |j|)^{-2}` is summable on `ℤ`.

This is the `ℓ¹` hypothesis under which the convolution representation of the IW projection
`Π_{≤l,≤k}` converges absolutely for bounded inputs.
-/

/-- **`ℓ¹`-summability of the kernel of `iwSymbolSet A (bump L)`.** -/
theorem summable_iwKernel_iwSymbolSet_bump (A : Finset Work.Analysis.IonescuWainger.Circle) (L : ℕ) :
    Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j‖) := by
  -- The cutoff `η_{≤-L}` is `C²` with compact support.
  have hcd : ContDiff ℝ 2 (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
      (-(L : ℤ))) :=
    (Work.KMTAreas.A7.contDiff_etaCut _).of_le (WithTop.coe_le_coe.mpr le_top)
  have hcs : HasCompactSupport
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) :=
    Work.KMTAreas.A7.hasCompactSupport_etaCut _
  -- Comparison with the summable weight `j ↦ (1 + |j|)^{-2}`.
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (Work.KMTAreas.A7.summable_kmtKernWeight.mul_left
      (4 * ((A.card : ℝ) * max
        (∫ y, ‖Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ)) y‖)
        (∫ y, ‖iteratedDeriv 2 (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
          (-(L : ℤ))) y‖))))
  · have h := Work.KMTPlan.A6.iwKernelDecaySharp A hcd hcs j
    simpa only [Work.KMTPlan.A6.Decim.bump] using h

end Work.KMTAreas.A7Hi
