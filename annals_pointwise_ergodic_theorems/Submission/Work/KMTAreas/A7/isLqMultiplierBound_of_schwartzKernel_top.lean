import Mathlib
import Submission.Work.KMTAreas.A7.EtaMultAux
import Submission.Port.Aesm

/-!
# The `L^∞` endpoint of the Schwartz-kernel multiplier bound

`Work.Analysis.IWMultiplier.contMulOp φ` is the continuous Fourier multiplier with symbol `φ`,
and `Work.KMTAreas.A7.contMulOp_eq_convolution` identifies it with the convolution
`x ↦ ∫ t, f t • K (x - t)` whenever `𝓕 K = φ`.

The operator norm of that convolution on `L^∞(ℝ)` is at most the `L¹`-norm of the kernel: this is
Young's inequality at the endpoint `(p, r, q) = (∞, 1, ∞)`.  Consequently, whenever `K` is a
Schwartz function with `‖K‖_{L¹} ≤ M`, the symbol `φ = 𝓕 K` is an `L^∞`-multiplier with bound
`M`.  This file proves that endpoint; it is the `q = ⊤` companion of
`Work.KMTAreas.A7.isLqMultiplierBound_of_schwartzKernel`, which concerns `1 ≤ q < ∞`.

## Main results

* `Work.KMTAreas.A7.eLpNorm_conv_smul_le_top` — `‖K ⋆ f‖_∞ ≤ ‖K‖_1 ‖f‖_∞`, in the
  `MeasureTheory.eLpNorm` vocabulary.
* `Work.KMTAreas.A7.isLqMultiplierBound_of_schwartzKernel_top` — the `L^∞` endpoint of the
  multiplier bound.
-/

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal

/-- **Young's inequality at the endpoint `(∞,1,∞)`.**  For a continuous kernel `K` and any
function `f`, the `L^∞` seminorm of the convolution `x ↦ ∫ t, f t • K (x - t)` is bounded by the
product of the `L¹` seminorm of `K` and the `L^∞` seminorm of `f`.

No integrability of `f` is assumed: the pointwise estimate
`‖∫ t, f t • K (x - t)‖ ≤ ∫⁻ t, ‖f t‖ₑ ‖K (x - t)‖ₑ ≤ ‖f‖_∞ ∫⁻ t, ‖K (x - t)‖ₑ` is
unconditional, and `∫⁻ t, ‖K (x - t)‖ₑ = ∫⁻ t, ‖K t‖ₑ` by translation invariance of Lebesgue
measure. -/
lemma eLpNorm_conv_smul_le_top (K f : ℝ → ℂ) (hK : Continuous K)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x : ℝ => ∫ t, f t • K (x - t)) ⊤ volume
      ≤ eLpNorm K 1 volume * eLpNorm f ⊤ volume := by
  have hRHS : eLpNorm K 1 volume * eLpNorm f ⊤ volume
      = (∫⁻ t, ‖K t‖ₑ ∂volume) * essSup (fun t : ℝ => ‖f t‖ₑ) volume := by
    rw [eLpNorm_one_eq_lintegral_enorm (hf := hK.aestronglyMeasurable),
      eLpNorm_exponent_top (hf := hf), eLpNormEssSup_eq_essSup_enorm]
  have hconv : AEStronglyMeasurable (fun x : ℝ => ∫ t, f t • K (x - t)) volume := by
    have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2 • K (p.1 - p.2))
        (volume.prod volume) :=
      (hf.comp_snd (μ := (volume : Measure ℝ))).smul
        (hK.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    exact hprod.integral_prod_right'
  rw [hRHS, eLpNorm_exponent_top (hf := hconv)]
  refine eLpNormEssSup_le_of_ae_enorm_bound (C :=
    (∫⁻ t, ‖K t‖ₑ ∂volume) * essSup (fun t : ℝ => ‖f t‖ₑ) volume) ?_
  have hS : ∀ᵐ t ∂volume, ‖f t‖ₑ ≤ essSup (fun t : ℝ => ‖f t‖ₑ) volume :=
    ENNReal.ae_le_essSup _
  filter_upwards with x
  have hmeas : AEMeasurable (fun t : ℝ => ‖K (x - t)‖ₑ) volume :=
    ((hK.comp (continuous_const.sub continuous_id)).enorm).aemeasurable
  calc ‖∫ t : ℝ, f t • K (x - t)‖ₑ
      ≤ ∫⁻ t, ‖f t • K (x - t)‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t, ‖f t‖ₑ * ‖K (x - t)‖ₑ ∂volume := by
        refine lintegral_congr fun t => ?_
        rw [enorm_smul]
    _ ≤ ∫⁻ t, (essSup (fun t : ℝ => ‖f t‖ₑ) volume) * ‖K (x - t)‖ₑ ∂volume := by
        refine lintegral_mono_ae ?_
        filter_upwards [hS] with t ht
        exact mul_le_mul_left ht _
    _ = (essSup (fun t : ℝ => ‖f t‖ₑ) volume) * ∫⁻ t, ‖K (x - t)‖ₑ ∂volume :=
        lintegral_const_mul'' _ hmeas
    _ = (essSup (fun t : ℝ => ‖f t‖ₑ) volume) * ∫⁻ t, ‖K t‖ₑ ∂volume := by
        rw [lintegral_sub_left_eq_self (fun w : ℝ => ‖K w‖ₑ) x]
    _ = (∫⁻ t, ‖K t‖ₑ ∂volume) * essSup (fun t : ℝ => ‖f t‖ₑ) volume := mul_comm _ _

/-- **The `L^∞` endpoint of the Schwartz-kernel multiplier bound.**  If the symbol `φ` is the
Fourier transform of a Schwartz function `K` whose `L¹` norm is at most `M`, then the Fourier
multiplier `T_φ = 𝓕⁻ ∘ (φ · 𝓕)` is bounded on `L^∞(ℝ)` with norm at most `M`.

Indeed `T_φ` is the convolution with `K` (`contMulOp_eq_convolution`), and Young's inequality at
the endpoint `(∞, 1, ∞)` bounds the `L^∞` operator norm of that convolution by `‖K‖_{L¹} ≤ M`. -/
theorem isLqMultiplierBound_of_schwartzKernel_top {K : SchwartzMap ℝ ℂ} {φ : ℝ → ℂ} {M : NNReal}
    (hφ : ∀ ξ : ℝ, FourierTransform.fourier (K : ℝ → ℂ) ξ = φ ξ)
    (hKM : MeasureTheory.eLpNorm (K : ℝ → ℂ) 1 MeasureTheory.volume ≤ ENNReal.ofReal (M : ℝ)) :
    Work.Analysis.IWMultiplier.IsLqMultiplierBound ⊤ φ M := by
  intro f
  rw [Work.KMTAreas.A7.contMulOp_eq_convolution K φ hφ f]
  simp only [MeasureTheory.convolution_lsmul]
  calc eLpNorm (fun x : ℝ => ∫ t, (f : ℝ → ℂ) t • (K : ℝ → ℂ) (x - t)) ⊤ volume
      ≤ eLpNorm (K : ℝ → ℂ) 1 volume * eLpNorm (f : ℝ → ℂ) ⊤ volume :=
        eLpNorm_conv_smul_le_top (K : ℝ → ℂ) (f : ℝ → ℂ) K.continuous
          f.continuous.aestronglyMeasurable
    _ ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) ⊤ volume :=
        mul_le_mul_left hKM _

end Work.KMTAreas.A7
