import Mathlib

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

end Commons.Analysis.Fourier
