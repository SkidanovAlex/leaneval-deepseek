/-
# `ℓ¹`-theory of the discrete convolution: `zConvL1`

For `w, g : ℤ → ℂ` with `w ∈ ℓ¹`, `g ∈ ℓ¹` and `‖g‖_∞ ≤ 1`, the convolution
`(w * g)(x) = ∑_m w m · g (x - m)` satisfies

* `x ↦ ‖(w * g)(x)‖` is summable and `∑_x ‖(w * g)(x)‖ ≤ ‖w‖₁ ‖g‖₁` (Young's inequality);
* `‖(w * g)(x)‖ ≤ ‖w‖₁` for every `x` (the `ℓ¹ * ℓ^∞ → ℓ^∞` bound);
* `𝓕_ℤ (w * g) = 𝓕_ℤ w · 𝓕_ℤ g` (the Fourier transform turns convolution into multiplication).

The first two statements are the `Q = 1` case of `lipSmoothOpTsumLe` for the smoothing operator
`smoothOp` (`∑_m w m G (x - Q m)`), after identifying `smoothOp w g 1` with the ordinary
convolution; the Fourier identity is the `Q = 1` case of `lipZFourierSmoothOp` together with
`𝓕_ℤ w ξ = ∑_m w m e(-m ξ)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lipSmoothOpTsumLe
import Submission.Work.KMTAreas.A4.lipZFourierSmoothOp

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The smoothing operator at the scale `Q = 1` is the ordinary convolution
`x ↦ ∑_m w m * G (x - m)`. -/
theorem smoothOp_one_eq_conv (w G : ℤ → ℂ) :
    smoothOp w G 1 = fun x : ℤ => ∑' m : ℤ, w m * G (x - m) := by
  funext x
  rw [smoothOp]
  exact tsum_congr fun m => by rw [one_mul]

/-- **The Fourier transform of a convolution.** For absolutely summable `w, g : ℤ → ℂ` the
Fourier transform of the convolution `x ↦ ∑_m w m * g (x - m)` is the product of the Fourier
transforms. -/
theorem zFourier_conv_eq_mul (w g : ℤ → ℂ) (hw : Summable fun m : ℤ => ‖w m‖)
    (hg : Summable fun x : ℤ => ‖g x‖) (ξ : FreqCircle) :
    ZFourier (fun x : ℤ => ∑' m : ℤ, w m * g (x - m)) ξ = ZFourier w ξ * ZFourier g ξ := by
  have h := lipZFourierSmoothOp hw hg 1 ξ
  rw [smoothOp_one_eq_conv] at h
  have hsum : (∑' m : ℤ, w m * (fourier (-(1 * m)) ξ : ℂ)) = ZFourier w ξ := by
    rw [ZFourier]
    exact tsum_congr fun m => by rw [one_mul]
  rw [h, hsum, mul_comm]

theorem zConvL1 (w g : ℤ → ℂ) (hw : Summable fun m : ℤ => ‖w m‖) (hg : Summable fun m : ℤ => ‖g m‖) (hg1 : ∀ m : ℤ, ‖g m‖ ≤ 1) : Summable (fun x : ℤ => ‖∑' m : ℤ, w m * g (x - m)‖) ∧ (∑' x : ℤ, ‖∑' m : ℤ, w m * g (x - m)‖ ≤ (∑' m : ℤ, ‖w m‖) * ∑' m : ℤ, ‖g m‖) ∧ (∀ x : ℤ, ‖∑' m : ℤ, w m * g (x - m)‖ ≤ ∑' m : ℤ, ‖w m‖) ∧ (∀ ξ : Work.Analysis.InverseTheory.FreqCircle, Work.Analysis.InverseTheory.ZFourier (fun x : ℤ => ∑' m : ℤ, w m * g (x - m)) ξ = Work.Analysis.InverseTheory.ZFourier w ξ * Work.Analysis.InverseTheory.ZFourier g ξ) := by
  have hYoung := lipSmoothOpTsumLe hw hg 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [smoothOp_one_eq_conv] using hYoung.1
  · simpa only [smoothOp_one_eq_conv] using hYoung.2
  · intro x
    have hlt : ∀ m : ℤ, ‖w m‖ * ‖g (x - m)‖ ≤ ‖w m‖ := fun m => by
      calc ‖w m‖ * ‖g (x - m)‖ ≤ ‖w m‖ * 1 :=
            mul_le_mul_of_nonneg_left (hg1 (x - m)) (norm_nonneg (w m))
        _ = ‖w m‖ := mul_one _
    have hsum : Summable fun m : ℤ => ‖w m * g (x - m)‖ :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _)
        (fun m => by rw [norm_mul]; exact hlt m) hw
    calc ‖∑' m : ℤ, w m * g (x - m)‖
        ≤ ∑' m : ℤ, ‖w m * g (x - m)‖ := norm_tsum_le_tsum_norm hsum
      _ = ∑' m : ℤ, ‖w m‖ * ‖g (x - m)‖ := tsum_congr fun m => norm_mul _ _
      _ ≤ ∑' m : ℤ, ‖w m‖ := by
            refine Summable.tsum_le_tsum hlt ?_ hw
            exact Summable.of_nonneg_of_le
              (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hlt hw
  · intro ξ
    exact zFourier_conv_eq_mul w g hw hg ξ

end Work.KMTAreas.A4
