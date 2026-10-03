import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded

/-!
# Sharp quadratic decay of the Ionescu–Wainger kernel of a `C²` bump

The Ionescu–Wainger projection `T^{≤l}_φ` of §5 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022

is, on `ℓ^q(ℤ)`, convolution with the kernel `j ↦ iwKernel (iwSymbolSet A (periodize F)) j`, the
`j`-th Fourier coefficient of the symbol `ξ ↦ ∑_{α ∈ A} (periodize F)(ξ - α)`.  This file proves
the *sharp* quadratic decay of that kernel, with the explicit constant
`4 · (#A · max ‖F‖₁ ‖F´´‖₁)` (no additive constant), namely

`‖iwKernel (iwSymbolSet A (periodize F)) j‖ ≤ 4 · (#A · max ‖F‖₁ ‖F´´‖₁) · ‖kmtKernWeight j‖`

where `‖F‖₁ = ∫ ‖F‖`, `‖F´´‖₁ = ∫ ‖iteratedDeriv 2 F‖` and `kmtKernWeight j = (1 + |j|)^{-2}`.

The proof has three ingredients:

* the Poisson-summation identity `Work.KMTPlan.A6.iwKernel_periodize_fourier`, identifying the
  kernel with `𝓕 G j` for the sum of translates `G y = ∑_{α ∈ A} F (y - a_α)`;
* the **sharp** quadratic Fourier decay `fourierDecaySharp` of a `C²` compactly supported function
  `g`, with the constant `4 · max ‖g‖₁ ‖g´´‖₁` — i.e. `Work.KMTAreas.A7.FourierDecayExplicit`
  with the spurious `+ 1` removed.  The sharp form is what lets the constant depend on `A` only
  through the factor `#A`;
* the two `L¹` bounds `integral_norm_sum_kmtTransl_le` and
  `integral_norm_iteratedDeriv_sum_kmtTransl_le` of `Work.KMTAreas.A7.KmtKernelL1Uniform`.

This is the form of the estimate requested by `Work.KMTPlan.A6.iwKernelDecaySharp`; compare
`Work.KMTAreas.A7.iwKernel_decay_of_bump`, which is the same statement with the weaker constant
`4 · (#A · S) + 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped FourierTransform

namespace Work.KMTPlan.A6

/-- **Quadratic decay of the Fourier transform, with the sharp constant.**  For a `C²` function
`g : ℝ → ℂ` with compact support and every `x : ℝ`,

`‖𝓕 g x‖ ≤ 4 · max (∫ ‖g‖) (∫ ‖g´´‖) / (1 + |x|)²`.

The proof is the same integration by parts as in `Work.KMTAreas.A7.FourierDecayExplicit`, but the
two cases `|x| ≤ 1` and `|x| > 1` are compared directly with `4 · max ‖g‖₁ ‖g´´‖₁` instead of
with `4 · max ‖g‖₁ ‖g´´‖₁ + 1`: near `x = 0` one uses `(1 + |x|)² ≤ 4` and the `L¹` bound for `g`,
far from `0` one uses `(1 + |x|)² ≤ (2π|x|)²` and the `L¹` bound for `g´´`. -/
theorem fourierDecaySharp {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g)
    (x : ℝ) :
    ‖FourierTransform.fourier g x‖ ≤
      4 * max (∫ y, ‖g y‖) (∫ y, ‖iteratedDeriv 2 g y‖) / (1 + |x|) ^ 2 := by
  set A := ∫ y, ‖g y‖ with hA
  set B := ∫ y, ‖iteratedDeriv 2 g y‖ with hB
  have hAnn : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun y => norm_nonneg _)
  -- Integrability of `g` and of its first two iterated derivatives.
  have hg0 : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  have h2eq : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hcomp2 : HasCompactSupport (iteratedDeriv 2 g) := by
    rw [h2eq]; exact hc.deriv.deriv
  have hg2 : Integrable (iteratedDeriv 2 g) :=
    (hg.continuous_iteratedDeriv 2 (by norm_num)).integrable_of_hasCompactSupport hcomp2
  have hInt : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable (iteratedDeriv n g) := by
    intro n hn
    have hn' : n ≤ 2 := by exact_mod_cast hn
    interval_cases n
    · rw [iteratedDeriv_zero]; exact hg0
    · have hc1 : HasCompactSupport (iteratedDeriv 1 g) := by
        rw [iteratedDeriv_one]; exact hc.deriv
      exact (hg.continuous_iteratedDeriv 1 (by norm_num)).integrable_of_hasCompactSupport hc1
    · exact hg2
  -- The Fourier transform of the second derivative.
  have hF2 : 𝓕 (iteratedDeriv 2 g) =
      fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))^2 • 𝓕 g x :=
    Real.fourier_iteratedDeriv (N := 2) (n := 2) hg hInt (by norm_num)
  -- `L¹` bound for `g` itself.
  have hbd1 : ‖𝓕 g x‖ ≤ A := by
    rw [hA]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  -- `L¹` bound for the second derivative, transferred to `𝓕 g x`.
  have hF2x : 𝓕 (iteratedDeriv 2 g) x =
      (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))^2 • 𝓕 g x := congr_fun hF2 x
  have hnorm : ‖𝓕 (iteratedDeriv 2 g) x‖ = (2 * Real.pi * |x|)^2 * ‖𝓕 g x‖ := by
    rw [hF2x, norm_smul, norm_pow]
    congr 1
    have h1 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have h2 : ‖(Real.pi : ℂ)‖ = |Real.pi| := RCLike.norm_ofReal Real.pi
    have h3 : ‖((x : ℝ) : ℂ)‖ = |x| := RCLike.norm_ofReal x
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, h1, h2, h3,
      abs_of_nonneg Real.pi_pos.le]
  have hbd2 : (2 * Real.pi * |x|)^2 * ‖𝓕 g x‖ ≤ B := by
    rw [← hnorm, hB]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have hmaxAB : 0 ≤ max A B := le_trans hAnn (le_max_left A B)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + |x|)^2)]
  by_cases hx : |x| ≤ 1
  · -- Small `x`: the `L¹` bound for `g` suffices, together with `(1 + |x|)² ≤ 4`.
    have h4 : (1 + |x|)^2 ≤ 4 := by nlinarith [abs_nonneg x, hx]
    have hstep : ‖𝓕 g x‖ * (1 + |x|)^2 ≤ A * 4 := by
      calc ‖𝓕 g x‖ * (1 + |x|)^2 ≤ A * (1 + |x|)^2 :=
            mul_le_mul_of_nonneg_right hbd1 (by positivity)
        _ ≤ A * 4 := mul_le_mul_of_nonneg_left h4 hAnn
    have hAm : A ≤ max A B := le_max_left A B
    linarith
  · -- Large `x`: the `L¹` bound for the second derivative, with `(1 + |x|)² ≤ (2π|x|)²`.
    have hx' : 1 < |x| := not_le.mp hx
    have h4 : (1 + |x|)^2 ≤ (2 * Real.pi * |x|)^2 := by
      have h5 : 1 + |x| ≤ 2 * Real.pi * |x| := by
        have h6 : 1 + |x| ≤ 2 * |x| := by linarith
        have h7 : 2 * |x| ≤ 2 * Real.pi * |x| := by
          have h8 : (2 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
          exact mul_le_mul_of_nonneg_right h8 (abs_nonneg x)
        linarith
      have h9 : (0 : ℝ) ≤ 1 + |x| := by positivity
      exact pow_le_pow_left₀ h9 h5 2
    have hBm : B ≤ max A B := le_max_right A B
    calc ‖𝓕 g x‖ * (1 + |x|)^2
          ≤ ‖𝓕 g x‖ * (2 * Real.pi * |x|)^2 := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = (2 * Real.pi * |x|)^2 * ‖𝓕 g x‖ := by ring
      _ ≤ B := hbd2
      _ ≤ 4 * max A B := by linarith

/-- **Sharp quadratic decay of the kernel of the Ionescu–Wainger symbol of a `C²` bump.**  For a
`C²` function `F : ℝ → ℂ` with compact support and any finite set `A` of circle frequencies,

`‖iwKernel (iwSymbolSet A (periodize F)) j‖
  ≤ 4 · (#A · max ‖F‖₁ ‖F´´‖₁) · ‖kmtKernWeight j‖`. -/
theorem iwKernelDecaySharp (A : Finset Work.Analysis.IonescuWainger.Circle) {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFs : HasCompactSupport F) (j : ℤ) :
    ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize F)) j‖
    ≤ 4 * ((A.card : ℝ) * max (∫ y, ‖F y‖) (∫ y, ‖iteratedDeriv 2 F y‖))
      * ‖Work.KMTAreas.A7.kmtKernWeight j‖ := by
  -- The function on `ℝ` whose Fourier transform is the kernel.
  set G : ℝ → ℂ :=
    fun y => ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val) with hGdef
  have hGcd : ContDiff ℝ 2 G := by
    rw [hGdef]
    exact ContDiff.sum (fun α _ => hF.comp (contDiff_id.sub contDiff_const))
  -- A radius outside which `F` vanishes, and the corresponding bound for `G`.
  obtain ⟨R, hR⟩ := Work.KMTAreas.A7.exists_abs_le_of_hasCompactSupport hFs
  have hGzero : ∀ y : ℝ, R + 1 ≤ |y| → G y = 0 := by
    rw [hGdef]; intro y hy
    refine Finset.sum_eq_zero (fun α _ => hR _ ?_)
    have h1 : |(AddCircle.equivIco (1 : ℝ) 0 α).val| ≤ 1 :=
      Work.KMTAreas.A7.abs_kmtFreqRep_le_one α
    have h2 : |y| - |(AddCircle.equivIco (1 : ℝ) 0 α).val| ≤
        |y - (AddCircle.equivIco (1 : ℝ) 0 α).val| := abs_sub_abs_le_abs_sub y _
    linarith
  have hGcs : HasCompactSupport G := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-(R + 1)) (R + 1)) isCompact_Icc ?_
    intro y hy
    have h : ¬ (R + 1 ≤ |y|) := fun hh => hy (hGzero y hh)
    rw [not_le, abs_lt] at h
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  -- The two `L¹` bounds.
  have hInt1 : (∫ y, ‖G y‖) ≤ (A.card : ℝ) * ∫ y, ‖F y‖ :=
    Work.KMTAreas.A7.integral_norm_sum_kmtTransl_le A F hF.continuous hFs
  have hInt2 : (∫ y, ‖iteratedDeriv 2 G y‖)
      ≤ (A.card : ℝ) * ∫ y, ‖iteratedDeriv 2 F y‖ :=
    Work.KMTAreas.A7.integral_norm_iteratedDeriv_sum_kmtTransl_le A F hF hFs
  have hmax : max (∫ y, ‖G y‖) (∫ y, ‖iteratedDeriv 2 G y‖)
      ≤ (A.card : ℝ) * max (∫ y, ‖F y‖) (∫ y, ‖iteratedDeriv 2 F y‖) := by
    refine max_le ?_ ?_
    · exact le_trans hInt1 (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _))
    · exact le_trans hInt2 (mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _))
  have hpos : (0 : ℝ) < (1 + |(j : ℝ)|) ^ 2 := by positivity
  have hdec := fourierDecaySharp hGcd hGcs (j : ℝ)
  have hkey : ‖FourierTransform.fourier G (j : ℝ)‖ ≤
      4 * ((A.card : ℝ) * max (∫ y, ‖F y‖) (∫ y, ‖iteratedDeriv 2 F y‖))
        / (1 + |(j : ℝ)|) ^ 2 := by
    rw [le_div_iff₀ hpos]
    calc ‖FourierTransform.fourier G (j : ℝ)‖ * (1 + |(j : ℝ)|) ^ 2
        ≤ 4 * max (∫ y, ‖G y‖) (∫ y, ‖iteratedDeriv 2 G y‖) :=
          (le_div_iff₀ hpos).mp hdec
      _ ≤ 4 * ((A.card : ℝ) * max (∫ y, ‖F y‖) (∫ y, ‖iteratedDeriv 2 F y‖)) :=
          mul_le_mul_of_nonneg_left hmax (by norm_num)
  calc ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize F)) j‖
      = ‖FourierTransform.fourier G (j : ℝ)‖ := by
        rw [iwKernel_periodize_fourier A hF.continuous hFs j]
    _ ≤ 4 * ((A.card : ℝ) * max (∫ y, ‖F y‖) (∫ y, ‖iteratedDeriv 2 F y‖))
          / (1 + |(j : ℝ)|) ^ 2 := hkey
    _ = 4 * ((A.card : ℝ) * max (∫ y, ‖F y‖) (∫ y, ‖iteratedDeriv 2 F y‖))
          * ‖Work.KMTAreas.A7.kmtKernWeight j‖ := by
        rw [Work.KMTAreas.A7.norm_kmtKernWeight j]
        ring

end Work.KMTPlan.A6
