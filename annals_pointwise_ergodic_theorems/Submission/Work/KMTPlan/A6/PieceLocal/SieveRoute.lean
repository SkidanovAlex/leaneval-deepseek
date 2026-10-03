/-
# Local repair of the sieve route (`Work.KMTAreas.A7Hi2.sieveRouteUnconditional`)

`Submission/Work/KMTAreas/A7Hi2/sieveRouteUnconditional.lean` (another area's module) is currently
**broken**: its two proofs apply a lemma whose conclusion is `∃ C, 0 < C ∧ ∀ l₁ m₀, …` directly to
the pair `(l₁, m₀)` (the `∃`-witness has to be extracted first), so the module does not compile and
has no `.olean`, which makes every module importing it (in particular
`…PieceBoundedH.sliceGBound`, hence the model-side bounded-height estimate) unimportable.

This module is a *local* copy of the two statements, with the trivial `obtain` added and the
declarations renamed (`…_local`, namespace `Work.KMTPlan.A6.PieceLocal`) so that it cannot clash
with the original should that be repaired later.  The mathematical content is unchanged: the sieve
branch of the `lpf` (low-pass Ionescu--Wainger walk) variational and values-maximal bounds, with
the real-scale JSW input `Work.KMTAreas.A7Hi2.dilVarRealScale_prop` and the sieve decomposition
`Work.A7Hi2.sieveDecompHyp_holds` both proved.
-/
import Mathlib
import Submission.Work.A7Hi2.SieveAssembly
import Submission.Work.KMTAreas.A7Hi2.dilVarRealScaleFinal

namespace Work.KMTPlan.A6.PieceLocal

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The decimated dilation bound, unconditional** (the `DilVarRealScale` input discharged by the
proved `Work.KMTAreas.A7Hi2.dilVarRealScale_prop`). -/
theorem decimDilBound_uncond_local : Work.A7Hi2.DecimDilBound :=
  Work.A7Hi2.decimDilBound_of_dilVarRealScale Work.KMTAreas.A7Hi2.dilVarRealScale_prop

/-- **The sieve bound for the variational norm, unconditional.** -/
theorem eLpNorm_variationalNorm_lpf_le_sieveMass_local
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r) (p : ℝ) (hp : 1 < p)
    (l₁ m₀ : ℕ)
    (hlarge : ∀ d ∈ Work.A7Hi2.iwDivs ρ l₁, Work.A7Hi2.sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Work.A7Hi2.sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ :=
    Work.A7Hi2.eLpNorm_variationalNorm_lpf_le_sieveMass_of_dilVarRealScale
      Work.KMTAreas.A7Hi2.dilVarRealScale_prop Work.A7Hi2.sieveDecompHyp_holds
      ρ hρ hρ1 r hr p hp
  exact ⟨C, hCpos, hC l₁ m₀ hlarge⟩

/-- **The values-maximal bound with the sieve constant, unconditional.** -/
theorem eLpNorm_supPart_lpf_le_sieveMass_local
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (p : ℝ) (hp : 1 < p)
    (l₁ m₀ : ℕ)
    (hlarge : ∀ d ∈ Work.A7Hi2.iwDivs ρ l₁, Work.A7Hi2.sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Work.A7Hi2.sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ :=
    Work.A7Hi2.eLpNorm_supPart_lpf_le_sieveMass
      Work.KMTAreas.A7Hi2.dilVarRealScale_prop Work.A7Hi2.sieveDecompHyp_holds
      ρ hρ hρ1 r p hp
  exact ⟨C, hCpos, hC l₁ m₀ hlarge⟩

end

end Work.KMTPlan.A6.PieceLocal
