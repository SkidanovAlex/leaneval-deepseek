import Mathlib
import Submission.Work.KMTContract.Areas
import Submission.Work.KMTAreas.A4.iwSymbolSetNegEq

/-!
# Reflection commutes with the Ionescu--Wainger projection `Π_{≤l,≤k}`

The Ionescu--Wainger projection `kmtProj ρ l k = Π_{≤l,≤k}` of Krause--Mirek--Tao §5 is the
convolution with the Fourier coefficients `iwKernel (iwSymbolSet (iwArithFreqs ρ l)
(periodize (etaCut kmtEta k)))` of the IW symbol `σ_{l,k}(ξ) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(ξ - α)`.

The symbol is **even** in the frequency (`iwSymbolSetNegEq`), because `(ℚ/ℤ)_{≤l}` is invariant
under `α ↦ -α` and the cutoff `η_{≤k}` is even.  For the Fourier coefficients of an even symbol on
the circle, the change of variable `ξ ↦ -ξ` (Haar measure on the circle is invariant under
negation) gives that the convolution kernel is even,

`iwKernel m (-j) = iwKernel m j` (`iwKernel_even_of_even`).

Since reflection `f ↦ (x ↦ f (-x))` is exactly the reindexing `j ↦ -j` of the convolution index,
`kmtProj ρ l k` commutes with reflection: the main result of this file is

`kmtProj_reflect : kmtProj ρ l k (fun x => f (-x)) = fun x => kmtProj ρ l k f (-x)`.

This is the (elementary, but unavoidable) reflection-compatibility used by the symmetrisation
steps of §5, which pass between a function and its reflection.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTAreas.A4

open MeasureTheory
open Work.Analysis.IonescuWainger

/-- **The Fourier-coefficient kernel of an even circle symbol is even.**  For a symbol `m` on the
circle with `m (-ξ) = m ξ` the Fourier coefficients `iwKernel m j = m̂(j)` satisfy
`iwKernel m (-j) = iwKernel m j`: substitute `ξ ↦ -ξ` in the defining integral (Haar measure on
the circle is invariant under negation) and use `fourier n (-ξ) = fourier (-n) ξ`. -/
lemma iwKernel_even_of_even {m : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hm : ∀ ξ, m (-ξ) = m ξ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel m (-j) = Work.Analysis.IWMultiplier.iwKernel m j := by
  have hkey : ∀ n : ℤ, Work.Analysis.IWMultiplier.iwKernel m n
      = ∫ t : Work.Analysis.IonescuWainger.Circle,
          (fourier (-n)) t • m t ∂circleMeasure := fun n => rfl
  have hflip : ∀ (n : ℤ) (x : Work.Analysis.IonescuWainger.Circle),
      (fourier n) (-x) = (fourier (-n)) x := by
    intro n x
    simp [fourier_apply, smul_neg]
  rw [hkey, hkey]
  calc ∫ t : Work.Analysis.IonescuWainger.Circle,
        (fourier (-(-j))) t • m t ∂circleMeasure
      = ∫ t : Work.Analysis.IonescuWainger.Circle,
        (fourier j) t • m t ∂circleMeasure := by rw [neg_neg]
    _ = ∫ t : Work.Analysis.IonescuWainger.Circle,
        (fourier j) (-t) • m (-t) ∂circleMeasure :=
        (integral_neg_eq_self
          (fun t : Work.Analysis.IonescuWainger.Circle => (fourier j) t • m t)
          circleMeasure).symm
    _ = ∫ t : Work.Analysis.IonescuWainger.Circle,
        (fourier (-j)) t • m (-t) ∂circleMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [hflip j t]
    _ = ∫ t : Work.Analysis.IonescuWainger.Circle,
        (fourier (-j)) t • m t ∂circleMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [hm t]

/-- **Reindexing a convolution sum under `j ↦ -j`.**  For an even kernel `K` and any sequence
`g`, the sum `∑'_j K_j g_j` equals `∑'_j K_j g_{-j}` (the equivalence `j ↦ -j` of `ℤ`). -/
lemma tsum_mul_neg_of_even (K g : ℤ → ℂ) (hK : ∀ j : ℤ, K (-j) = K j) :
    (∑' j : ℤ, K j * g j) = ∑' j : ℤ, K j * g (-j) := by
  calc ∑' j : ℤ, K j * g j
      = ∑' j : ℤ, K ((Equiv.neg ℤ) j) * g ((Equiv.neg ℤ) j) :=
        (Equiv.tsum_eq (Equiv.neg ℤ) (fun j : ℤ => K j * g j)).symm
    _ = ∑' j : ℤ, K j * g (-j) := by
        refine tsum_congr fun j => ?_
        rw [Equiv.neg_apply, hK j]

theorem kmtProj_reflect (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) : Work.KMTContract.kmtProj ρ l k (fun x : ℤ => f (-x)) = fun x : ℤ => Work.KMTContract.kmtProj ρ l k f (-x) := by
  funext n
  simp only [Work.KMTContract.kmtProj_apply]
  have hK : ∀ j : ℤ,
      Work.Analysis.IWMultiplier.iwKernel
          (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))) (-j)
        = Work.Analysis.IWMultiplier.iwKernel
          (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))) j :=
    fun j => iwKernel_even_of_even (fun ξ => iwSymbolSetNegEq ρ l k ξ) j
  calc ∑' j : ℤ,
        Work.Analysis.IWMultiplier.iwKernel
            (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))) j
          * (fun x : ℤ => f (-x)) (n - j)
      = ∑' j : ℤ,
        Work.Analysis.IWMultiplier.iwKernel
            (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))) j
          * f (j - n) := by
        refine tsum_congr fun j => ?_
        simp only [neg_sub]
    _ = ∑' j : ℤ,
        Work.Analysis.IWMultiplier.iwKernel
            (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))) j
          * f (-j - n) :=
        tsum_mul_neg_of_even _ _ hK
    _ = ∑' j : ℤ,
        Work.Analysis.IWMultiplier.iwKernel
            (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))) j
          * f (-n - j) := by
        refine tsum_congr fun j => ?_
        rw [show -j - n = -n - j by ring]

end Work.KMTAreas.A4
