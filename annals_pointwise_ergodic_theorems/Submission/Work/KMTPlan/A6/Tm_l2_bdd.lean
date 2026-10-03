/-
# The `ℓ²`-boundedness of the exact-height Ionescu--Wainger multiplier `Tm ρ l φ`

Target: for every `ρ : ℝ`, `l : ℕ` and `S ≥ 0` there is `C ≥ 0` such that

`‖Tm ρ l φ f‖_{ℓ²(ℤ)} ≤ C ‖f‖_{ℓ²(ℤ)}`

for every `C²` compactly supported symbol `φ : ℝ → ℂ` with `∫‖φ‖ ≤ S`, `∫‖φ''‖ ≤ S` and every
`f ∈ ℓ²(ℤ)`.

The multiplier `Tm ρ l φ = iwConv (diffFreqs ρ l) (periodize φ)` is convolution with the kernel
`κ j = iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ)) j`, whose quadratic decay
`‖κ j‖ ≤ (4 · card(A) · S + 1)/(1+|j|)²` is the content of `iwKernel_decay_of_bump`.  In
particular `κ ∈ ℓ¹(ℤ)` with a bound depending only on `ρ, l, S`, and the **sup norm of the
multiplier symbol is bounded by the `ℓ¹` norm of the kernel**:

`‖iwSymbolSet A (periodize φ) ξ‖ ≤ ∑'_j ‖κ j‖`,

because the symbol is a continuous function on the circle whose Fourier coefficients are
`κ j` (`iwKernel m j = fourierCoeff m j` by definition) and those coefficients are absolutely
summable, so the Fourier series converges to it normally (`has_pointwise_sum_fourier_series_of_summable`).

With the symbol bound `M`, the `ℓ²` bound follows from the elementary Plancherel argument
`Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallSymDefs
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport
import Submission.Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound
import Submission.Work.KMTAreas.A7.tsum_norm_iwKernel_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- The Ionescu--Wainger symbol of a continuous symbol on the circle is continuous. -/
theorem continuous_iwSymbolSet (A : Finset Work.Analysis.IonescuWainger.Circle)
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} (hΦ : Continuous Φ) :
    Continuous (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) := by
  rw [show Work.Analysis.IonescuWainger.iwSymbolSet A Φ
      = fun ξ => ∑ α ∈ A, Φ (ξ - α) from rfl]
  exact continuous_finsetSum _ (fun α _ => hΦ.comp (continuous_id.sub continuous_const))

/-- **The sup norm of the IW symbol is bounded by the `ℓ¹` norm of its kernel.**  If the Fourier
coefficients `j ↦ iwKernel (iwSymbolSet A (periodize F)) j` of the symbol are absolutely
summable, then the symbol is bounded pointwise by their sum, because the Fourier series of the
(continuous) symbol converges to it normally. -/
theorem norm_iwSymbolSet_le_tsum_iwKernel
    (A : Finset Work.Analysis.IonescuWainger.Circle) {F : ℝ → ℂ} (hFc : Continuous F)
    (hFcs : HasCompactSupport F)
    (hκ : Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize F)) j‖) :
    ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize F) ξ‖
        ≤ ∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A
              (Work.Analysis.IonescuWainger.periodize F)) j‖ := by
  intro ξ
  -- The symbol as a continuous map on the circle.
  have hmcont : Continuous (Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize F)) :=
    continuous_iwSymbolSet A (continuous_periodize_of_hasCompactSupport F hFc hFcs)
  let m : C(Work.Analysis.IonescuWainger.Circle, ℂ) :=
    ⟨Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize F), hmcont⟩
  have hmcoe : (m : Work.Analysis.IonescuWainger.Circle → ℂ)
      = Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize F) := rfl
  -- Absolute summability of the Fourier coefficients of `m`.
  have hκ' : Summable fun j : ℤ => ‖fourierCoeff (⇑m) j‖ := by
    simpa only [Work.Analysis.IWMultiplier.iwKernel, hmcoe] using hκ
  -- Pointwise convergence of the Fourier series.
  have hpt := has_pointwise_sum_fourier_series_of_summable hκ'.of_norm ξ
  -- The Fourier characters have unit modulus.
  have hfourier : ∀ i : ℤ, ‖(fourier i) ξ‖ = 1 := by
    intro i
    rw [fourier_apply, Circle.norm_coe]
  have hmain : ‖(m : Work.Analysis.IonescuWainger.Circle → ℂ) ξ‖
      ≤ ∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A
            (Work.Analysis.IonescuWainger.periodize F)) j‖ := by
    calc ‖(m : Work.Analysis.IonescuWainger.Circle → ℂ) ξ‖
        = ‖∑' i : ℤ, fourierCoeff (⇑m) i • (fourier i) ξ‖ := by rw [hpt.tsum_eq]
      _ ≤ ∑' i : ℤ, ‖fourierCoeff (⇑m) i • (fourier i) ξ‖ :=
            norm_tsum_le_tsum_norm hpt.summable.norm
      _ = ∑' i : ℤ, ‖fourierCoeff (⇑m) i‖ := by
            refine tsum_congr (fun i => ?_)
            rw [norm_smul, hfourier i, mul_one]
      _ = ∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A
              (Work.Analysis.IonescuWainger.periodize F)) j‖ := by
            refine tsum_congr (fun j => ?_)
            simp only [Work.Analysis.IWMultiplier.iwKernel, hmcoe]
  simpa only [hmcoe] using hmain

theorem Tm_l2_bdd (ρ : ℝ) (l : ℕ) (S : ℝ) (hSnn : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : ℝ → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y : ℝ, ‖φ y‖) ≤ S → (∫ y : ℝ, ‖iteratedDeriv 2 φ y‖) ≤ S →
      ∀ (f : ℤ → ℂ), MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l φ f) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  -- The height-`l` arithmetic frequency set and the kernel-decay comparison constant.
  set A : Finset Work.Analysis.IonescuWainger.Circle := Work.KMTAreas.A7.diffFreqs ρ l with hA
  set K : ℝ := ∑' j : ℤ, ‖Work.KMTAreas.A7.kmtKernWeight j‖ with hK
  have hKnn : 0 ≤ K := by rw [hK]; exact tsum_nonneg (fun j => norm_nonneg _)
  set M : ℝ := (4 * ((A.card : ℝ) * S) + 1) * K with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  refine ⟨M, hMnn, ?_⟩
  intro φ hφcd hφcs h1 h2 f hf
  -- The kernel of the multiplier has quadratic decay, hence is in `ℓ¹`.
  have hdec : ∀ j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize φ)) j‖
      ≤ (4 * ((A.card : ℝ) * S) + 1) * ‖Work.KMTAreas.A7.kmtKernWeight j‖ :=
    Work.KMTAreas.A7.iwKernel_decay_of_bump A hφcd hφcs hSnn h1 h2
  have hκ : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize φ)) j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec
      (Work.KMTAreas.A7.summable_kmtKernWeight.mul_left _)
  -- The sup norm of the symbol, bounded by the `ℓ¹` norm of the kernel.
  have hbound : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize φ) ξ‖ ≤ M := by
    intro ξ
    refine (norm_iwSymbolSet_le_tsum_iwKernel A hφcd.continuous hφcs hκ ξ).trans ?_
    have hsum := Summable.tsum_le_tsum hdec hκ
      (Work.KMTAreas.A7.summable_kmtKernWeight.mul_left _)
    rw [tsum_mul_left] at hsum
    calc (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A
              (Work.Analysis.IonescuWainger.periodize φ)) j‖)
        ≤ (4 * ((A.card : ℝ) * S) + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.kmtKernWeight j‖) := hsum
      _ = M := by rw [hM, hK]
  have hcont : Continuous (Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize φ)) :=
    continuous_iwSymbolSet A (continuous_periodize_of_hasCompactSupport φ hφcd.continuous hφcs)
  have hMem : MemLp (Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize φ)) ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
    MemLp.of_bound hcont.aestronglyMeasurable M (ae_of_all _ hbound)
  have hkey := eLpNorm_iwConv_two_le_of_symbol_bound A
    (Work.Analysis.IonescuWainger.periodize φ) M hMnn hbound hMem f hf
  have hTm : Work.KMTAreas.A7.Tm ρ l φ f
      = Work.Analysis.IWMultiplier.iwConv A
        (Work.Analysis.IonescuWainger.periodize φ) f := rfl
  rw [hTm]
  exact hkey

end Work.KMTPlan.A6
