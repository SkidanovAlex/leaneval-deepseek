import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Work.KMTPlan.A6.memlpOfMemLpCount

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IWMultiplier (iwKernel iwConv iwConv_apply)
open Work.Analysis.IonescuWainger (periodize iwSymbolSet circleMeasure)

/-! ## Cauchy--Schwarz for `ℓ²` sequences

The key point of the `ℓ²` form of additivity is that the summands of `iwConv` are products
`κ j * f (n - j)` of two `ℓ²` sequences, hence absolutely summable: `ℓ² * ℓ² ⊆ ℓ¹`.  This is the
only place where the hypothesis `f ∈ ℓ²` (rather than boundedness of `f`) is used. -/

/-- **`ℓ² * ℓ² ⊆ ℓ¹`**: the pointwise product of two square-summable sequences is summable.
Proof: `‖κ j‖ ‖z j‖ ≤ ‖κ j‖² + ‖z j‖²` (AM--GM), and the right-hand side is summable. -/
theorem summable_mul_of_summable_normSq {κ z : ℤ → ℂ}
    (hκ : Summable fun j : ℤ => ‖κ j‖ ^ 2) (hz : Summable fun j : ℤ => ‖z j‖ ^ 2) :
    Summable fun j : ℤ => κ j * z j := by
  refine Summable.of_norm ?_
  have hbound : ∀ j : ℤ, ‖κ j‖ * ‖z j‖ ≤ ‖κ j‖ ^ 2 + ‖z j‖ ^ 2 := by
    intro j
    nlinarith [sq_nonneg (‖κ j‖ - ‖z j‖)]
  have hsum : Summable fun j : ℤ => ‖κ j‖ * ‖z j‖ :=
    Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
      (hκ.add hz)
  simpa only [norm_mul] using hsum

/-- The same statement with the scalar multiplication of `iwConv`: the family
`j ↦ κ j • z j` is summable under square-summability of `κ` and `z`. -/
theorem summable_smul_of_summable_normSq {κ z : ℤ → ℂ}
    (hκ : Summable fun j : ℤ => ‖κ j‖ ^ 2) (hz : Summable fun j : ℤ => ‖z j‖ ^ 2) :
    Summable fun j : ℤ => κ j • z j := by
  simpa only [smul_eq_mul] using summable_mul_of_summable_normSq hκ hz

/-! ## Additivity of the periodisation and of the kernels -/

/-- Additivity of the periodisation `periodize φ ξ = ∑'_j φ (x + j)` for functions whose
translates are summable at every point. -/
theorem periodize_add' {φ ψ : ℝ → ℂ} (hφ : ∀ x : ℝ, Summable fun j : ℤ => φ (x + j))
    (hψ : ∀ x : ℝ, Summable fun j : ℤ => ψ (x + j)) :
    periodize (φ + ψ) = periodize φ + periodize ψ := by
  funext ξ
  simp only [periodize, Pi.add_apply]
  exact (hφ _).tsum_add (hψ _)

/-- Additivity of the Fourier-coefficient kernel of `iwSymbolSet A` in the symbol, for
integrable symbols. -/
theorem iwKernel_iwSymbolSet_add' {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ Ψ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hΦ : Integrable (iwSymbolSet A Φ) circleMeasure)
    (hΨ : Integrable (iwSymbolSet A Ψ) circleMeasure) (j : ℤ) :
    iwKernel (iwSymbolSet A (Φ + Ψ)) j
      = iwKernel (iwSymbolSet A Φ) j + iwKernel (iwSymbolSet A Ψ) j := by
  have hsym : iwSymbolSet A (Φ + Ψ) = iwSymbolSet A Φ + iwSymbolSet A Ψ :=
    Work.Analysis.IonescuWainger.iwSymbolSet_add A Φ Ψ
  simp only [iwKernel]
  rw [hsym, congrFun (fourierCoeff.add hΦ hΨ) j, Pi.add_apply]

/-- The `ℓ²`-summability of the kernel of the exact-height piece, transported to the translate
`j ↦ n - j` of the input. -/
theorem summable_kernel_translate {f : ℤ → ℂ} (hf : Summable fun j : ℤ => ‖f j‖ ^ 2) (n : ℤ) :
    Summable fun j : ℤ => ‖f (n - j)‖ ^ 2 :=
  hf.comp_injective (sub_right_injective (b := n))

open MeasureTheory in
open scoped ENNReal NNReal BigOperators in
/-- **Additivity of the Ionescu--Wainger multiplier family `Tm` in its symbol, for `ℓ²` input.**
Unlike the unconditional form, this needs the kernel families to be square-summable (so that the
unconditional `tsum`s defining `Tm` may be added). -/
theorem Tm_add_of_memLp (ρ : ℝ) (l : ℕ) {φ ψ : ℝ → ℂ} {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hφ : ∀ x : ℝ, Summable fun j : ℤ => φ (x + j))
    (hψ : ∀ x : ℝ, Summable fun j : ℤ => ψ (x + j))
    (hIφ : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) Work.Analysis.IonescuWainger.circleMeasure)
    (hIψ : Integrable (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize ψ)) Work.Analysis.IonescuWainger.circleMeasure)
    (hκφ : Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize φ)) j‖ ^ 2)
    (hκψ : Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize ψ)) j‖ ^ 2) :
    Work.KMTAreas.A7.Tm ρ l (φ + ψ) f
      = Work.KMTAreas.A7.Tm ρ l φ f + Work.KMTAreas.A7.Tm ρ l ψ f := by
  -- `f ∈ ℓ²` with respect to the counting measure means `∑ ‖f j‖² < ∞`.
  have hfmem : Memℓp f (2 : ℝ≥0∞) :=
    memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf
  have hf2 : Summable fun j : ℤ => ‖f j‖ ^ 2 := by
    have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp hfmem
    simpa [Real.rpow_natCast] using h
  -- Additivity of the symbol at the level of the Fourier coefficients.
  have hsym : Work.Analysis.IonescuWainger.periodize (φ + ψ)
      = Work.Analysis.IonescuWainger.periodize φ
        + Work.Analysis.IonescuWainger.periodize ψ :=
    periodize_add' hφ hψ
  funext n
  have hzf : Summable fun j : ℤ => ‖f (n - j)‖ ^ 2 := summable_kernel_translate hf2 n
  have hs1 : Summable fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) j • f (n - j) :=
    summable_smul_of_summable_normSq hκφ hzf
  have hs2 : Summable fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize ψ)) j • f (n - j) :=
    summable_smul_of_summable_normSq hκψ hzf
  simp only [Work.KMTAreas.A7.Tm, iwConv_apply, Pi.add_apply]
  rw [hsym, ← hs1.tsum_add hs2]
  refine tsum_congr (fun j => ?_)
  rw [iwKernel_iwSymbolSet_add' hIφ hIψ j, add_smul]

end Work.KMTPlan.A6
