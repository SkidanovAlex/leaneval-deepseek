import Mathlib
import Submission.Commons.Analysis.Fourier.lintegral_fourierInv_eq

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform ENNReal

/-!
# `L²` modulus of continuity of band-limited functions

If `G ∈ L¹ ∩ L²(ℝ)` has Fourier transform supported in `[-a,a]`, then translating `G` by `y`
changes it in `L²` by at most `2πa|y|` in relative size.  The proof is Plancherel's theorem
combined with the elementary bound `‖e^{iθ} - 1‖ ≤ |θ|` on the phase factor of a translation.
-/

set_option maxHeartbeats 1000000

lemma fourierChar_sub_one_norm_le (t : ℝ) :
    ‖(Real.fourierChar t : ℂ) - 1‖ ≤ 2 * Real.pi * |t| := by
  rw [Real.fourierChar_apply]
  rw [show (↑(2 * Real.pi * t) : ℂ) * Complex.I = Complex.I * ↑(2 * Real.pi * t) by rw [mul_comm]]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t)
  refine h.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]

lemma fourier_comp_add_right_real (g : ℝ → ℂ) (y ξ : ℝ) :
    𝓕 (fun x => g (x + y)) ξ = (Real.fourierChar (y * ξ) : ℂ) • 𝓕 g ξ := by
  change VectorFourier.fourierIntegral (Real.fourierChar) volume (innerₗ ℝ)
      (g ∘ fun v => v + y) ξ
    = (Real.fourierChar (y * ξ) : ℂ) • VectorFourier.fourierIntegral (Real.fourierChar) volume (innerₗ ℝ) g ξ
  rw [VectorFourier.fourierIntegral_comp_add_right (V := ℝ) (W := ℝ) (E := ℂ)
    (𝕜 := ℝ) (e := Real.fourierChar) (μ := volume) (L := innerₗ ℝ) g y]
  dsimp only
  rw [show ((innerₗ ℝ) y) ξ = ξ * y from rfl, mul_comm ξ y, Circle.smul_def]

lemma lintegral_fourier_sq_eq {h : ℝ → ℂ} (h1 : MemLp h 1 (volume : Measure ℝ))
    (h2 : MemLp h 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖𝓕 h x‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) := by
  calc ∫⁻ x, ‖𝓕 h x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ‖𝓕 h (-x)‖ₑ ^ (2:ℝ) :=
        (lintegral_neg_eq_self (fun x : ℝ => ‖𝓕 h x‖ₑ ^ (2:ℝ))).symm
    _ = ∫⁻ x, ‖𝓕⁻ h x‖ₑ ^ (2:ℝ) := by
        apply lintegral_congr; intro x; rw [Real.fourierInv_eq_fourier_neg]
    _ = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) := by
        simpa only [ofReal_norm, ENNReal.rpow_natCast] using lintegral_fourierInv_eq h1 h2

/-- **Energy of a translate of a band-limited `L²` function.**  If `G ∈ L¹ ∩ L²(ℝ)` has Fourier
transform supported in `[-a,a]`, then translating `G` by `y` changes it in `L²` by at most
`2πa|y|` in relative size: this is the quantitative form of the fact that a band-limited function
is Lipschitz of order `1` in `L²` with the bandwidth as constant. -/
theorem lintegral_translate_sub_sq_le_of_fourier_support {G : ℝ → ℂ}
    (hG1 : Integrable G) (hG2 : MemLp G 2 (volume : Measure ℝ)) {a y : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ ξ : ℝ, a < |ξ| → 𝓕 G ξ = 0) :
    ∫⁻ x, ‖G (x + y) - G x‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) := by
  set f : ℝ → ℂ := fun x => G (x + y) - G x with hfdef
  change ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ)
  have hG1' : MemLp G 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hG1
  have hGy_int : Integrable (fun x => G (x + y)) := hG1.comp_add_right y
  have hf_int : Integrable f := by rw [hfdef]; exact hGy_int.sub hG1
  have hf1 : MemLp f 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hf_int
  have hGy2 : MemLp (fun x => G (x + y)) 2 (volume : Measure ℝ) :=
    hG2.comp_measurePreserving (measurePreserving_add_right volume y)
  have hf2 : MemLp f 2 (volume : Measure ℝ) := by rw [hfdef]; exact hGy2.sub hG2
  -- Fourier transform of `f`
  have hsplit : 𝓕 f = 𝓕 (fun x => G (x + y)) - 𝓕 G := by
    have hsum : 𝓕 (f + G) = 𝓕 f + 𝓕 G := by
      change VectorFourier.fourierIntegral (Real.fourierChar) volume (innerₗ ℝ) (f + G)
        = VectorFourier.fourierIntegral (Real.fourierChar) volume (innerₗ ℝ) f
          + VectorFourier.fourierIntegral (Real.fourierChar) volume (innerₗ ℝ) G
      exact VectorFourier.fourierIntegral_add Real.continuous_fourierChar (by fun_prop) hf_int hG1
    rw [show f + G = fun x => G (x + y) from by funext x; simp [hfdef]] at hsum
    exact eq_sub_iff_add_eq.mpr hsum.symm
  have hpt : ∀ ξ : ℝ, 𝓕 f ξ = ((Real.fourierChar (y * ξ) : ℂ) - 1) * 𝓕 G ξ := by
    intro ξ
    rw [hsplit, Pi.sub_apply, fourier_comp_add_right_real G y ξ, smul_eq_mul]
    ring
  have hbound : ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ (2 * Real.pi * a * |y|) * ‖𝓕 G ξ‖ := by
    intro ξ
    rw [hpt ξ, norm_mul]
    by_cases hξ : |ξ| ≤ a
    · have h2 : ‖(Real.fourierChar (y * ξ) : ℂ) - 1‖ ≤ 2 * Real.pi * a * |y| := by
        refine (fourierChar_sub_one_norm_le (y * ξ)).trans ?_
        rw [abs_mul]
        calc 2 * Real.pi * (|y| * |ξ|) = (2 * Real.pi * |y|) * |ξ| := by ring
          _ ≤ (2 * Real.pi * |y|) * a := mul_le_mul_of_nonneg_left hξ (by positivity)
          _ = 2 * Real.pi * a * |y| := by ring
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    · rw [hsupp ξ (lt_of_not_ge hξ)]; simp
  have hC_nonneg : (0:ℝ) ≤ 2 * Real.pi * a * |y| := by positivity
  have hconst : (ENNReal.ofReal (2 * Real.pi * a * |y|)) ^ (2:ℝ)
      = ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) := by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hC_nonneg]
  -- measurability of the Fourier energy
  have hcont : Continuous (𝓕 G) := by
    change Continuous (VectorFourier.fourierIntegral (Real.fourierChar) volume (innerₗ ℝ) G)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hG1
  have hmeas : Measurable (fun ξ : ℝ => ‖𝓕 G ξ‖ₑ ^ (2:ℝ)) := by
    have h1 : Measurable (fun ξ : ℝ => ‖𝓕 G ξ‖ₑ) := hcont.enorm.measurable
    have h2 : Measurable (fun ξ : ℝ => ‖𝓕 G ξ‖ₑ * ‖𝓕 G ξ‖ₑ) := h1.mul h1
    simpa only [ENNReal.rpow_two, pow_two] using h2
  have hstep : ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ∫⁻ ξ, ‖𝓕 G ξ‖ₑ ^ (2:ℝ) := by
    have hpt2 : ∀ ξ : ℝ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ)
        ≤ ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ‖𝓕 G ξ‖ₑ ^ (2:ℝ) := by
      intro ξ
      have hle : ‖𝓕 f ξ‖ₑ ≤ ENNReal.ofReal (2 * Real.pi * a * |y|) * ‖𝓕 G ξ‖ₑ := by
        rw [← ofReal_norm (𝓕 f ξ), ← ofReal_norm (𝓕 G ξ)]
        calc ENNReal.ofReal ‖𝓕 f ξ‖
            ≤ ENNReal.ofReal ((2 * Real.pi * a * |y|) * ‖𝓕 G ξ‖) :=
              ENNReal.ofReal_le_ofReal (hbound ξ)
          _ = ENNReal.ofReal (2 * Real.pi * a * |y|) * ENNReal.ofReal ‖𝓕 G ξ‖ :=
              ENNReal.ofReal_mul hC_nonneg
      calc ‖𝓕 f ξ‖ₑ ^ (2:ℝ)
          ≤ (ENNReal.ofReal (2 * Real.pi * a * |y|) * ‖𝓕 G ξ‖ₑ) ^ (2:ℝ) :=
            ENNReal.rpow_le_rpow hle (by norm_num)
        _ = (ENNReal.ofReal (2 * Real.pi * a * |y|)) ^ (2:ℝ) * ‖𝓕 G ξ‖ₑ ^ (2:ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        _ = ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ‖𝓕 G ξ‖ₑ ^ (2:ℝ) := by
            rw [hconst]
    calc ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ‖𝓕 G ξ‖ₑ ^ (2:ℝ) :=
          lintegral_mono hpt2
      _ = ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ∫⁻ ξ, ‖𝓕 G ξ‖ₑ ^ (2:ℝ) :=
          lintegral_const_mul _ hmeas
  calc ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ‖𝓕 f x‖ₑ ^ (2:ℝ) := (lintegral_fourier_sq_eq hf1 hf2).symm
    _ ≤ ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ∫⁻ x, ‖𝓕 G x‖ₑ ^ (2:ℝ) := hstep
    _ = ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ∫⁻ x, ‖G x‖ₑ ^ (2:ℝ) := by
        rw [lintegral_fourier_sq_eq hG1' hG2]

end Commons.Analysis.Fourier
