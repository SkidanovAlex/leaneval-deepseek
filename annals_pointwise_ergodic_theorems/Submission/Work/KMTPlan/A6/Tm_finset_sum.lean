import Mathlib
import Submission.Work.KMTPlan.A6.Tm_add_of_memLp
import Submission.Work.KMTPlan.A6.LowSmallDefs

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IWMultiplier (iwKernel iwConv iwConv_apply)
open Work.Analysis.IonescuWainger (periodize iwSymbolSet circleMeasure)

/-! ## Linearity of the Ionescu--Wainger family `Tm` in its symbol

`Tm ρ l φ u = iwConv (diffFreqs ρ l) (periodize φ) u` is, for each `n`, the `tsum` of the
summands `iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ)) j • u (n - j)`.  Since `periodize`,
`iwSymbolSet` and `iwKernel` are all linear in the symbol, the whole family is linear in `φ`; the
only point that needs the hypothesis `f ∈ ℓ²` is the absolute summability of the summands, which
follows from `ℓ² * ℓ² ⊆ ℓ¹` (`summable_smul_of_summable_normSq`, proved in `Tm_add_of_memLp`).

The three lemmas below perform the linearity at the three levels: periodisation, IW symbol, and
Fourier coefficient. -/

/-- Linearity of the periodisation in the function: `periodize (∑ i∈s c i • φ i)` is the finite
combination of the periodisations, provided the translates of each `φ i` are summable. -/
theorem periodize_finset_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (φ : ι → ℝ → ℂ)
    (hφ : ∀ i ∈ s, ∀ x : ℝ, Summable fun j : ℤ => φ i (x + (j : ℝ))) :
    periodize (∑ i ∈ s, c i • φ i) = ∑ i ∈ s, c i • periodize (φ i) := by
  funext ξ
  simp only [periodize, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Summable.tsum_finsetSum
    (f := fun i (k : ℤ) => c i * φ i ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (k : ℝ)))
    (fun i hi => (hφ i hi _).mul_left (c i))]
  exact Finset.sum_congr rfl fun i _ => tsum_mul_left

/-- Linearity of the IW symbol `iwSymbolSet A Φ ξ = ∑_{α ∈ A} Φ (ξ - α)` in `Φ`. -/
theorem iwSymbolSet_finset_smul {ι : Type*} (A : Finset Work.Analysis.IonescuWainger.Circle)
    (s : Finset ι) (c : ι → ℂ) (Φ : ι → Work.Analysis.IonescuWainger.Circle → ℂ) :
    iwSymbolSet A (∑ i ∈ s, c i • Φ i) = ∑ i ∈ s, c i • iwSymbolSet A (Φ i) := by
  funext ξ
  simp only [iwSymbolSet, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum ..).symm

/-- Linearity of the Fourier-coefficient kernel `iwKernel` in the symbol, for integrable
symbols (the integrability is what the Finset version of `fourierCoeff.add` requires). -/
theorem iwKernel_finset_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (m : ι → Work.Analysis.IonescuWainger.Circle → ℂ)
    (hm : ∀ i ∈ s, Integrable (m i) circleMeasure) (j : ℤ) :
    iwKernel (∑ i ∈ s, c i • m i) j = ∑ i ∈ s, c i * iwKernel (m i) j := by
  simp only [iwKernel]
  rw [fourierCoeff.sum s (fun i => c i • m i) (fun i hi => (hm i hi).smul (c i))]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [fourierCoeff.const_smul, smul_eq_mul]

/-- **Finite linearity of the Ionescu--Wainger multiplier family `Tm` in its symbol.**

For `f ∈ ℓ²` and symbols whose periodisations have integrable IW symbol and square-summable IW
kernel, `Tm ρ l (∑ i∈s c i • φ i) f = ∑ i∈s c i • Tm ρ l (φ i) f`.  This generalises
`Tm_add_of_memLp` from two summands to an arbitrary finite `ℂ`-linear combination. -/
theorem Tm_finset_sum (ρ : Real) (l : ℕ) {ι : Type*} (s : Finset ι) (c : ι → Complex)
    (φ : ι → Real → Complex) (f : ℤ → Complex)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hφ : ∀ i ∈ s, ∀ x : Real, Summable fun j : ℤ => φ i (x + (j : Real)))
    (hI : ∀ i ∈ s, MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (φ i))) Work.Analysis.IonescuWainger.circleMeasure)
    (hκ : ∀ i ∈ s, Summable fun j : ℤ =>
      ‖Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (φ i))) j‖ ^ 2) :
    Work.KMTAreas.A7.Tm ρ l (∑ i ∈ s, c i • φ i) f
      = ∑ i ∈ s, c i • Work.KMTAreas.A7.Tm ρ l (φ i) f := by
  classical
  -- `f ∈ ℓ²` with respect to the counting measure means `∑ ‖f j‖² < ∞`.
  have hfmem : Memℓp f (2 : ℝ≥0∞) :=
    memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf
  have hf2 : Summable fun j : ℤ => ‖f j‖ ^ 2 := by
    have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp hfmem
    simpa [Real.rpow_natCast] using h
  funext n
  have hzf : Summable fun j : ℤ => ‖f (n - j)‖ ^ 2 := summable_kernel_translate hf2 n
  -- Linearity of the periodisation, the IW symbol and the kernel.
  have hper : periodize (∑ i ∈ s, c i • φ i) = ∑ i ∈ s, c i • periodize (φ i) :=
    periodize_finset_smul s c φ hφ
  have hsym : iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (∑ i ∈ s, c i • periodize (φ i))
      = ∑ i ∈ s, c i • iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (periodize (φ i)) :=
    iwSymbolSet_finset_smul _ s c _
  have hker : ∀ j : ℤ, iwKernel (∑ i ∈ s, c i • iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (periodize (φ i))) j
      = ∑ i ∈ s, c i * iwKernel (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (periodize (φ i))) j :=
    fun j => iwKernel_finset_smul s c _ (fun i hi => hI i hi) j
  simp only [Work.KMTAreas.A7.Tm, iwConv_apply]
  rw [hper, hsym]
  simp_rw [hker]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, iwConv_apply]
  -- Each summand `j ↦ c i * (κ i j * f (n - j))` is summable: `ℓ² * ℓ² ⊆ ℓ¹`.
  have hsummable : ∀ i ∈ s, Summable fun j : ℤ =>
      c i * (iwKernel (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (periodize (φ i))) j
        * f (n - j)) :=
    fun i hi => (summable_smul_of_summable_normSq (hκ i hi) hzf).mul_left (c i)
  -- Distribute the finite sum over the product and interchange `tsum` with the finite sum.
  have hLHS : (∑' (j : ℤ), (∑ i ∈ s, c i * iwKernel (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (periodize (φ i))) j) * f (n - j))
      = ∑' (j : ℤ), ∑ i ∈ s, c i * (iwKernel (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (periodize (φ i))) j * f (n - j)) := by
    refine tsum_congr fun j => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  rw [hLHS]
  rw [Summable.tsum_finsetSum (f := fun i (j : ℤ) => c i *
      (iwKernel (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (periodize (φ i))) j
        * f (n - j))) hsummable]
  exact Finset.sum_congr rfl fun i _ => tsum_mul_left

end Work.KMTPlan.A6
