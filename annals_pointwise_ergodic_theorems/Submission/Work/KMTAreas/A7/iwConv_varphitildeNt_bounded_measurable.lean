/-
# The `ℓ^∞` bound and the `t`-measurability of `iwConv A (periodize φ̃_{N,t})`

For an arbitrary finite set `A` of circle frequencies, the Ionescu--Wainger convolution operator
with the symbol `periodize φ̃_{N,t}` (the modulated bump `φ̃_{N,t}(ξ) = φ̃_N(ξ) e(P(Nt)ξ)`) is
bounded on `ℓ^∞(ℤ)` with a constant uniform in `t ∈ [1/2,1]` and in the position, and it depends
measurably on `t`.  This is the `A`-general form of
`Work.KMTAreas.A7.Tle_varphitildeNt_bounded` and
`Work.KMTAreas.A7.measurable_iwKernel_varphitildeNt`, needed for the exact-height frequency sets
`iwArithFreqsNew ρ l` of the §6 model operator.

## Proof

`iwConv A Φ g = ∑'_j iwKernel (iwSymbolSet A Φ) j * g(·-j)`; by
`Work.KMTPlan.A6.IwKernelArithChar` the kernel is the arithmetic character sum
`∑_{α∈A} e(-jα)` times `cw φ̃_{N,t} j = 𝓕 φ̃_{N,t} j`, and by the modulation rule
`𝓕 φ̃_{N,t} j = 𝓕 φ̃_N (j - P(Nt))` (`fourier_varphitildeNt_eq`).  The quadratic Fourier decay
`fourierDecay_varphitildeN` combined with the bound `|P(Nt)| ≤ M` gives a `t`-independent
`j^{-2}` decay of the kernel, hence an absolutely summable majorant
(`norm_tsum_kernel_mul_le`).  The measurability is the parametrised-integral argument of
`measurable_fourierCoeff_iwSymbolSet` plus `Measurable.tsum`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FiberGeneral
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphitildeNt

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- **The kernel identity at an arbitrary frequency set.**  The `j`-th Fourier coefficient of the
IW symbol of the modulated bump `φ̃_{N,t}` is the arithmetic character sum
`∑_{α ∈ A} e(-jα)` times the Fourier transform of the unmodulated bump at the shifted frequency
`j - c_t`, `c_t = PevalR P (N t)`. -/
theorem iwKernel_varphitildeNt_eq_general (P : Polynomial ℤ)
    (A : Finset Work.Analysis.IonescuWainger.Circle) (d N k : ℕ) (t : ℝ) (j : ℤ) :
    iwKernel (iwSymbolSet A (periodize (varphitildeNt P d N k t))) j
      = arithCharSet A (-j)
        * FourierTransform.fourier (varphitildeN d N k) ((j : ℝ) - PevalR P ((N : ℝ) * t)) := by
  have hid := Work.KMTPlan.A6.IwKernelArithChar A
    (integrable_varphitildeNt_aux P d N k t) j
  rw [hid, cw_eq_fourierTransform, arithCharSet]
  rw [show FourierTransform.fourier (varphitildeNt P d N k t) (j : ℝ)
      = FourierTransform.fourier (varphitildeN d N k) ((j : ℝ) - PevalR P ((N : ℝ) * t)) from
    fourier_varphitildeNt_eq P d N k t (j : ℝ)]

/-- **Quadratic decay of the kernel, uniformly in `t ∈ [1/2,1]` and in the frequency set.** -/
theorem iwKernel_varphitildeNt_decay (P : Polynomial ℤ)
    (A : Finset Work.Analysis.IonescuWainger.Circle) (d N k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet A (periodize (varphitildeNt P d N k t))) j‖
        ≤ C / (1 + |(j : ℝ)|) ^ 2 := by
  obtain ⟨Cf, hCfpos, hCfdec⟩ := fourierDecay_varphitildeN d N k
  set Mv : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
    (1 + (N : ℝ)) ^ P.natDegree) with hMv
  set K : ℝ := (2 * Mv + 1) ^ 2 with hK
  have hMnonneg : 0 ≤ Mv := le_trans zero_le_one (le_max_left 1 _)
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨(A.card : ℝ) * Cf * K + 1, by positivity, fun t ht j => ?_⟩
  have ht1 : |t| ≤ 1 := by
    obtain ⟨h1, h2⟩ := ht
    rw [abs_le]
    exact ⟨by linarith, h2⟩
  have hc : |PevalR P ((N : ℝ) * t)| ≤ Mv :=
    le_trans (abs_PevalR_mul_le P N ht1) (le_max_right 1 _)
  rw [iwKernel_varphitildeNt_eq_general P A d N k t j]
  have h1 : ‖arithCharSet A (-j)‖ ≤ (A.card : ℝ) := norm_arithCharSet_le A (-j)
  have h2 : ‖FourierTransform.fourier (varphitildeN d N k)
        ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ ≤ Cf * K / (1 + |(j : ℝ)|) ^ 2 := by
    refine le_trans (hCfdec ((j : ℝ) - PevalR P ((N : ℝ) * t))) ?_
    have hmaj := one_div_sq_le_of_abs_sub_le hMnonneg hc j
    calc Cf / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2
        = Cf * (1 / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2) := div_eq_mul_one_div _ _
      _ ≤ Cf * (K / (1 + |(j : ℝ)|) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hCfpos.le
          rw [hK]
          exact hmaj
      _ = Cf * K / (1 + |(j : ℝ)|) ^ 2 := (mul_div_assoc _ _ _).symm
  calc ‖arithCharSet A (-j) * FourierTransform.fourier (varphitildeN d N k)
          ((j : ℝ) - PevalR P ((N : ℝ) * t))‖
      = ‖arithCharSet A (-j)‖ * ‖FourierTransform.fourier (varphitildeN d N k)
          ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ := norm_mul _ _
    _ ≤ (A.card : ℝ) * (Cf * K / (1 + |(j : ℝ)|) ^ 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
    _ ≤ ((A.card : ℝ) * Cf * K + 1) / (1 + |(j : ℝ)|) ^ 2 := by
        have hpos : (0 : ℝ) < (1 + |(j : ℝ)|) ^ 2 := by positivity
        have hle : (A.card : ℝ) * Cf * K ≤ (A.card : ℝ) * Cf * K + 1 := by linarith
        refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hle hpos.le)
        ring

/-- **The `ℓ^∞` bound for `iwConv A (periodize φ̃_{N,t})`, uniform in `t ∈ [1/2,1]`.** -/
theorem iwConv_varphitildeNt_bounded (P : Polynomial ℤ)
    (A : Finset Work.Analysis.IonescuWainger.Circle) (d N k : ℕ) (g : ℤ → ℂ) (Cg : ℝ)
    (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖iwConv A (periodize (varphitildeNt P d N k t)) g y‖ ≤ C := by
  obtain ⟨Cκ, hCκpos, hdec⟩ := iwKernel_varphitildeNt_decay P A d N k
  refine ⟨Cκ * (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2) * max Cg 0, fun t ht y => ?_⟩
  have h := norm_tsum_kernel_mul_le (A := A) (Φ := periodize (varphitildeNt P d N k t))
    (v := g) (Cκ := Cκ) (B := Cg) (hdec t ht) hg y
  rw [iwConv]
  exact h

/-- **Measurability in `t` of the IW kernel of `φ̃_{N,t}`, for an arbitrary frequency set.** -/
theorem measurable_iwKernel_varphitildeNt_general (P : Polynomial ℤ)
    (A : Finset Work.Analysis.IonescuWainger.Circle) (N k : ℕ) (j : ℤ) :
    Measurable (fun t : ℝ => iwKernel
      (iwSymbolSet A (periodize (varphitildeNt P P.natDegree N k t))) j) := by
  have h := measurable_fourierCoeff_iwSymbolSet A j
    (φ := fun t ξ => varphitildeNt P P.natDegree N k t ξ) (measurable_varphitildeNt_uncurry P N k)
  simpa only [iwKernel] using h

/-- **Measurability in `t` of the values of `iwConv A (periodize φ̃_{N,t})`.** -/
theorem measurable_iwConv_varphitildeNt (P : Polynomial ℤ)
    (A : Finset Work.Analysis.IonescuWainger.Circle) (N k : ℕ) (g : ℤ → ℂ) (y : ℤ) :
    Measurable (fun t : ℝ => iwConv A (periodize (varphitildeNt P P.natDegree N k t)) g y) := by
  have hfun : (fun t : ℝ => iwConv A (periodize (varphitildeNt P P.natDegree N k t)) g y)
      = fun t : ℝ => ∑' j : ℤ,
          iwKernel (iwSymbolSet A (periodize (varphitildeNt P P.natDegree N k t))) j * g (y - j) := by
    funext t
    rw [iwConv]
    exact tsum_congr (fun j => smul_eq_mul _ _)
  rw [hfun]
  exact Measurable.tsum (fun j : ℤ =>
    (measurable_iwKernel_varphitildeNt_general P A N k j).mul measurable_const)

/-- **The `ℓ^∞` bound and the `t`-measurability of `iwConv A (periodize φ̃_{N,t})`.** -/
theorem iwConv_varphitildeNt_bounded_measurable (P : Polynomial ℤ)
    (A : Finset Work.Analysis.IonescuWainger.Circle)
    (N k : ℕ) (g : ℤ → ℂ) (Cg : ℝ) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) :
    (∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖iwConv A (periodize (varphitildeNt P P.natDegree N k t)) g y‖ ≤ C)
    ∧ (∀ y : ℤ, Measurable (fun t : ℝ => iwConv A
        (periodize (varphitildeNt P P.natDegree N k t)) g y)) := by
  exact ⟨iwConv_varphitildeNt_bounded P A P.natDegree N k g Cg hg,
    fun y => measurable_iwConv_varphitildeNt P A N k g y⟩

end

end Work.KMTAreas.A7
