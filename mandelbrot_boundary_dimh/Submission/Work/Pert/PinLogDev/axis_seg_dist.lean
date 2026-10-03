import Mathlib

namespace Work.Pert.PinLogDev

theorem axis_seg_dist {n c₁ c₂ : ℝ} {w z₁ z₂ : ℂ}
    (hwim : |w.im| = 1) (hc : c₁ ≤ c₂)
    (hre1 : 31 * n / 32 ≤ z₁.re) (hre1' : z₁.re ≤ 33 * n / 32)
    (hre2 : 31 * n / 32 ≤ z₂.re) (hre2' : z₂.re ≤ 33 * n / 32)
    (him1 : |z₁.im - c₁ * w.im| ≤ n / 32) (him2 : |z₂.im - c₂ * w.im| ≤ n / 32) :
    ‖z₂ - z₁‖ ≤ (c₂ - c₁) + n / 8 := by
  -- Real parts: both lie in the window `[31n/32, 33n/32]` of width `n/16`.
  have hre : |(z₂ - z₁).re| ≤ n / 16 := by
    rw [Complex.sub_re, abs_le]
    constructor <;> linarith
  -- Imaginary parts: each is within `n/32` of `cᵢ * w.im`, with `|w.im| = 1`, so the
  -- difference between the two references is at most `(c₂ - c₁)`.
  have him : |(z₂ - z₁).im| ≤ (c₂ - c₁) + n / 16 := by
    rw [Complex.sub_im]
    set A := z₂.im - c₂ * w.im with hA
    set B := z₁.im - c₁ * w.im with hB
    set C := (c₂ - c₁) * w.im with hC
    have hA' : |A| ≤ n / 32 := him2
    have hB' : |B| ≤ n / 32 := him1
    have hC'' : |C| ≤ c₂ - c₁ := by
      rw [hC, abs_mul, hwim, mul_one, abs_of_nonneg (by linarith)]
    have hkey : z₂.im - z₁.im = A + C - B := by rw [hA, hB, hC]; ring
    rw [hkey, abs_le]
    constructor <;> linarith [abs_le.mp hA', abs_le.mp hB', abs_le.mp hC'']
  calc ‖z₂ - z₁‖ ≤ |(z₂ - z₁).re| + |(z₂ - z₁).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ n / 16 + ((c₂ - c₁) + n / 16) := add_le_add hre him
    _ = (c₂ - c₁) + n / 8 := by ring

end Work.Pert.PinLogDev
