import Mathlib
import Submission.Work.KMTPlan.A6.Decim.Defs
import Submission.Work.KMTPlan.A6.Tm_l2_bdd

/-!
# The Fourier series of the Ionescu--Wainger symbol of the dyadic bump

The dyadic circle bump `Work.KMTPlan.A6.Decim.bump L = periodize (etaCut kmtEta (-(L:ℤ)))` is the
periodisation of the smooth compactly supported KMT cutoff `η_{≤-L}`, hence is a *continuous*
function on the circle (`Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport`, applied to
`Work.KMTAreas.A7.contDiff_etaCut` and `Work.KMTAreas.A7.hasCompactSupport_etaCut`).  So is the
Ionescu--Wainger symbol `iwSymbolSet A (bump L) = ∑_{α ∈ A} bump L (· - α)`, a finite sum of
translates of a continuous function (`Work.KMTPlan.A6.continuous_iwSymbolSet`).

The Ionescu--Wainger kernel is by definition the sequence of Fourier coefficients of the symbol,
`iwKernel m j = fourierCoeff m j`.  Consequently, whenever those coefficients are absolutely
summable (hypothesis `hκ`; this is *proved* in the sibling module
`Submission.Work.KMTAreas.A7Hi.summable_iwKernel_iwSymbolSet_bump`), the Fourier series of the
symbol converges absolutely and uniformly, and — because the limit is a continuous function on the
circle whose Fourier coefficients are, by construction, exactly the `iwKernel`s — it converges
*pointwise to the symbol itself*.  That is the statement of Mathlib's
`has_pointwise_sum_fourier_series_of_summable`, applied to the continuous map `⟨iwSymbolSet A
(bump L), hcont⟩`.
-/

namespace Work.KMTAreas.A7Hi

/-- **The Fourier series of the Ionescu--Wainger symbol of the dyadic bump.**  If the kernel of
`iwSymbolSet A (bump L)` is absolutely summable, then at every point of the circle the symbol is
the sum of its Fourier series. -/
theorem hasSum_fourierSeries_iwSymbolSet_bump (A : Finset Work.Analysis.IonescuWainger.Circle) (L : ℕ)
    (hκ : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j‖)) :
    ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      HasSum (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j
        * fourier (T := 1) j ξ)
        (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L) ξ) := by
  -- The symbol is continuous, being a finite sum of translates of the continuous periodisation of
  -- the compactly supported cutoff `η_{≤-L}`.
  have hcont : Continuous
      (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) :=
    Work.KMTPlan.A6.continuous_iwSymbolSet A
      (Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ)))
        (Work.KMTAreas.A7.contDiff_etaCut _).continuous
        (Work.KMTAreas.A7.hasCompactSupport_etaCut _))
  intro ξ
  -- The Fourier coefficients of the symbol are the Ionescu--Wainger kernel, which is summable.
  have hsum : Summable (fun j : ℤ =>
      fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.KMTPlan.A6.Decim.bump L)) j) := by
    refine Summable.of_norm ?_
    simpa only [Work.Analysis.IWMultiplier.iwKernel] using hκ
  -- Pointwise Fourier inversion for the continuous symbol.
  have hpt := has_pointwise_sum_fourier_series_of_summable
    (f := (⟨Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L),
      hcont⟩ : C(Work.Analysis.IonescuWainger.Circle, ℂ))) hsum ξ
  simpa only [Work.Analysis.IWMultiplier.iwKernel, smul_eq_mul, ContinuousMap.coe_mk] using hpt

end Work.KMTAreas.A7Hi
