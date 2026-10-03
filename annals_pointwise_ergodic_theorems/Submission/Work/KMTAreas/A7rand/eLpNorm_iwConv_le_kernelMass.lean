import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs
import Submission.Work.Analysis.Hilbert.ratio_multiplier_lp
import Submission.Port.Aesm

/-!
# Young's inequality for the Ionescu–Wainger convolution

`Work.Analysis.IWMultiplier.iwConv A Φ f` is the convolution of the sequence `f` with the kernel
`j ↦ iwKernel (iwSymbolSet A Φ) j` of the Ionescu–Wainger symbol.  Since a convolution with an
`ℓ¹` kernel is bounded on `ℓ^q` for every `1 ≤ q ≤ ∞` with the `ℓ¹` mass of the kernel as constant,
the `ℓ^q`-norm of `iwConv A Φ f` is bounded by
`(∑' j, ‖iwKernel (iwSymbolSet A Φ) j‖) * ‖f‖_{ℓ^q}`.

The `q = ⊤` case is proved directly from the pointwise bound (`enorm_tsum_le_tsum_enorm`) and
`enorm_le_eLpNorm_count`; the finite case is the already-proved Young inequality
`Work.Analysis.Hilbert.eLpNorm_conv_count_le` for convolution on `ℤ` with the counting measure.
-/

namespace Work.KMTAreas.A7rand

open MeasureTheory
open scoped ENNReal BigOperators

/-- Pointwise form of the `ℓ¹ ∗ ℓ^∞` bound: the absolute value of `iwConv A Φ f` at `n` is bounded
by the convolution of the moduli of the kernel and of `f`. -/
private lemma enorm_iwConv_le_tsum {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} (f : ℤ → ℂ) (n : ℤ) :
    ‖Work.Analysis.IWMultiplier.iwConv A Φ f n‖ₑ
      ≤ ∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖ₑ * ‖f (n - j)‖ₑ := by
  rw [Work.Analysis.IWMultiplier.iwConv_apply]
  refine (enorm_tsum_le_tsum_enorm).trans (le_of_eq ?_)
  exact tsum_congr fun j => by rw [smul_eq_mul, enorm_mul]

theorem eLpNorm_iwConv_le_kernelMass {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {q : ENNReal} (hq : 1 ≤ q) (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv A Φ f) q MeasureTheory.Measure.count
      ≤ (∑' j : ℤ, ENNReal.ofReal ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖)
        * MeasureTheory.eLpNorm f q MeasureTheory.Measure.count := by
  by_cases hqtop : q = ⊤
  · -- `q = ⊤`: bound the essential supremum pointwise
    subst hqtop
    rw [MeasureTheory.eLpNorm_exponent_top (hf := by pw_aesm)]
    refine MeasureTheory.eLpNormEssSup_le_of_ae_enorm_bound ?_
    filter_upwards with n
    calc ‖Work.Analysis.IWMultiplier.iwConv A Φ f n‖ₑ
        ≤ ∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖ₑ * ‖f (n - j)‖ₑ :=
          enorm_iwConv_le_tsum f n
      _ ≤ ∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖ₑ
              * MeasureTheory.eLpNorm f ⊤ MeasureTheory.Measure.count := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          gcongr
          exact MeasureTheory.enorm_le_eLpNorm_count f (n - j) (by simp)
      _ = (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖ₑ)
              * MeasureTheory.eLpNorm f ⊤ MeasureTheory.Measure.count :=
          ENNReal.tsum_mul_right
      _ = (∑' j : ℤ, ENNReal.ofReal ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖)
              * MeasureTheory.eLpNorm f ⊤ MeasureTheory.Measure.count := by
          rw [tsum_congr fun j => (ofReal_norm _).symm]
  · -- `q` finite: the Young inequality for convolution on `ℤ`
    have hconv : Work.Analysis.IWMultiplier.iwConv A Φ f
        = fun n : ℤ => ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j * f (n - j) := by
      funext n
      rw [Work.Analysis.IWMultiplier.iwConv_apply]
      exact tsum_congr fun j => by rw [smul_eq_mul]
    rw [hconv]
    have h1 : 1 ≤ q.toReal := by
      have := (ENNReal.toReal_le_toReal ENNReal.one_ne_top hqtop).mpr hq
      simpa using this
    have hqeq : ENNReal.ofReal q.toReal = q := ENNReal.ofReal_toReal hqtop
    have hmain := Work.Analysis.Hilbert.eLpNorm_conv_count_le (p := q.toReal) h1
      (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j) f
    rw [hqeq] at hmain
    exact hmain

end Work.KMTAreas.A7rand
