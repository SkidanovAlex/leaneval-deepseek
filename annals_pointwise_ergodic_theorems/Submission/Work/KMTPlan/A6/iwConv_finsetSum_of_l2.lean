/-
# Linearity of the Ionescu--Wainger convolution in a finite signed sum of symbols, for `ℓ²` input

The `ℓ¹`-kernel version of this statement is `Work.KMTAreas.A7.iwConv_finsetSum_of_bounded_lin`
(which needs the individual kernels to be absolutely summable, hence a Schwartz/narrow hypothesis on
the symbols).  Here the symbols are arbitrary `L²(circle)` functions and the input only has to be in
`ℓ²(ℤ)`: the summands `κ i j * f (n - j)` of the two `tsum`s are then products of two `ℓ²`
sequences, hence absolutely summable (`summable_mul_of_summable_normSq`), which is what makes the
interchange of the finite sum with the `tsum` legitimate.  This is the same argument as
`Tm_finset_sum` (which proves the statement for `Tm` over `diffFreqs ρ l`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.Tm_finset_sum

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IWMultiplier (iwKernel iwConv iwConv_apply)
open Work.Analysis.IonescuWainger (iwSymbolSet circleMeasure)

/-- **Linearity of the Ionescu--Wainger convolution `iwConv` in a finite signed sum of symbols, for
`ℓ²` input.** -/
theorem iwConv_finsetSum_of_l2 {ι : Type*}
    (A : Finset Work.Analysis.IonescuWainger.Circle) (s : Finset ι) (c : ι → ℂ)
    (Φ : ι → Work.Analysis.IonescuWainger.Circle → ℂ) (f : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hInt : ∀ i ∈ s, MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet A (Φ i))
      Work.Analysis.IonescuWainger.circleMeasure)
    (hκ : ∀ i ∈ s, Summable fun j : ℤ =>
      ‖Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A (Φ i)) j‖ ^ 2) :
    (∑ i ∈ s, c i • Work.Analysis.IWMultiplier.iwConv A (Φ i) f)
      = Work.Analysis.IWMultiplier.iwConv A (fun ξ => ∑ i ∈ s, c i * Φ i ξ) f := by
  classical
  have hfmem : Memℓp f (2 : ℝ≥0∞) :=
    memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf
  have hf2 : Summable fun j : ℤ => ‖f j‖ ^ 2 := by
    have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp hfmem
    simpa [Real.rpow_natCast] using h
  funext n
  have hL : (∑ i ∈ s, c i • iwConv A (Φ i) f) n
      = ∑ i ∈ s, c i * (∑' j : ℤ, iwKernel (iwSymbolSet A (Φ i)) j * f (n - j)) := by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, iwConv_apply]
    simp only [smul_eq_mul]
  have hsym : iwSymbolSet A (fun ξ => ∑ i ∈ s, c i * Φ i ξ)
      = ∑ i ∈ s, c i • iwSymbolSet A (Φ i) := by
    have hfun : (fun ξ => ∑ i ∈ s, c i * Φ i ξ) = (∑ i ∈ s, c i • Φ i) := by
      funext ξ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact iwSymbolSet_finset_smul A s c Φ
  have hR : iwConv A (fun ξ => ∑ i ∈ s, c i * Φ i ξ) f n
      = ∑ i ∈ s, c i * (∑' j : ℤ, iwKernel (iwSymbolSet A (Φ i)) j * f (n - j)) := by
    rw [iwConv_apply]
    simp only [smul_eq_mul]
    have h1 : (∑' j : ℤ, iwKernel (iwSymbolSet A (fun ξ => ∑ i ∈ s, c i * Φ i ξ)) j * f (n - j))
        = ∑' j : ℤ, ∑ i ∈ s, (c i * iwKernel (iwSymbolSet A (Φ i)) j) * f (n - j) := by
      refine tsum_congr (fun j => ?_)
      rw [hsym, iwKernel_finset_smul s c (fun i => iwSymbolSet A (Φ i)) hInt j, Finset.sum_mul]
    have hSumm : ∀ i ∈ s, Summable (fun j : ℤ =>
        (c i * iwKernel (iwSymbolSet A (Φ i)) j) * f (n - j)) := by
      intro i hi
      have hzf : Summable fun j : ℤ => ‖f (n - j)‖ ^ 2 := summable_kernel_translate hf2 n
      have hker : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A (Φ i)) j‖ ^ 2 := hκ i hi
      exact ((summable_mul_of_summable_normSq hker hzf).mul_left (c i)).congr
        (fun j => by ring)
    rw [h1, Summable.tsum_finsetSum (f := fun i : ι => fun j : ℤ =>
      (c i * iwKernel (iwSymbolSet A (Φ i)) j) * f (n - j)) hSumm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← tsum_mul_left]
    exact tsum_congr (fun j => by ring)
  rw [hL, hR]

end Work.KMTPlan.A6
