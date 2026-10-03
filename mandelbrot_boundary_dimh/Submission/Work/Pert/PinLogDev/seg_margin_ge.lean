import Mathlib
import Submission.Work.Pert.PinLogDev.Helpers

namespace Work.Pert.PinLogDev

/-!
# `seg_margin_ge`: the gate clearance survives on the whole segment

If the two endpoints `z₁`, `z₂` of a segment have real parts in the window
`[31 N/32, 33 N/32]` (`N = Nlen Rde`) and imaginary parts within `N/32` of the two heights
`c₁ w.im`, `c₂ w.im` with `|w.im| = 1`, `c₁, c₂ ≥ Y₀`, and the geometric condition

`34 N + 32 + 32 √2 Rde ≤ 32 (Y₀ - Ξ)`

holds, then every point of the segment has both gate margins `≥ √2 Rde`, where

* `margA Ξ α z = z.re - Ξ + (1/α).re + |z.im + (1/α).im|`,
* `margB Ξ α z = |z.im| - Ξ - z.re`.

The two estimates are

* `margA ≥ z.re + Cα ≥ 31 N/32 ≥ √2 Rde + 1` (using `(1/α).re = Cα + Ξ`, `Cα > 0`, and the
  defining property `N ≥ 32 (√2 Rde + 1)/31` of `Nlen`), and
* `margB ≥ (Y₀ - Ξ) - 17 N/16 ≥ 1 + √2 Rde` (using `|z.im| ≥ Y₀ - N/32`, `z.re ≤ 33 N/32`
  and the geometric hypothesis).
-/

/-- The real part of a point of the segment `z₁ + s • (z₂ - z₁)`. -/
private lemma seg_re_eq (z₁ z₂ : ℂ) (s : ℝ) :
    (z₁ + s • (z₂ - z₁)).re = (1 - s) * z₁.re + s * z₂.re := by
  rw [Complex.add_re, Complex.real_smul, Complex.mul_re]
  simp
  ring

/-- The imaginary part of a point of the segment `z₁ + s • (z₂ - z₁)`. -/
private lemma seg_im_eq (z₁ z₂ : ℂ) (s : ℝ) :
    (z₁ + s • (z₂ - z₁)).im = (1 - s) * z₁.im + s * z₂.im := by
  rw [Complex.add_im, Complex.real_smul, Complex.mul_im]
  simp
  ring

theorem seg_margin_ge
    {Ξ Rde Cα Y₀ c₁ c₂ : ℝ} {α w z₁ z₂ : ℂ}
    (hRde : 0 < Rde) (hΞ0 : 0 < Ξ) (hCα0 : 0 < Cα)
    (hCα : Cα = (1 / α).re - Ξ)
    (hwim : |w.im| = 1)
    (hgeo : 34 * (Nlen Rde : ℝ) + 32 + 32 * Real.sqrt 2 * Rde ≤ 32 * (Y₀ - Ξ))
    (hY1 : Y₀ ≤ c₁) (hY2 : Y₀ ≤ c₂)
    (hre1 : 31 * (Nlen Rde : ℝ) / 32 ≤ z₁.re)
    (hre1' : z₁.re ≤ 33 * (Nlen Rde : ℝ) / 32)
    (hre2 : 31 * (Nlen Rde : ℝ) / 32 ≤ z₂.re)
    (hre2' : z₂.re ≤ 33 * (Nlen Rde : ℝ) / 32)
    (him1 : |z₁.im - c₁ * w.im| ≤ (Nlen Rde : ℝ) / 32)
    (him2 : |z₂.im - c₂ * w.im| ≤ (Nlen Rde : ℝ) / 32)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt 2 * Rde ≤ min (Work.Pert.margA Ξ α (z₁ + s • (z₂ - z₁)))
      (Work.Pert.margB Ξ α (z₁ + s • (z₂ - z₁))) := by
  obtain ⟨hs0, hs1⟩ := hs
  set N : ℝ := (Nlen Rde : ℝ) with hNdef
  have hRde0 : 0 ≤ Rde := le_of_lt hRde
  have hsq2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hS0 : 0 < Real.sqrt 2 * Rde := mul_pos hsq2 hRde
  -- the defining lower bound for `Nlen`
  have hNceil : 32 * (Real.sqrt 2 * Rde + 1) / 31 ≤ N := by
    rw [hNdef]; exact Nat.le_ceil _
  have hNlow : Real.sqrt 2 * Rde + 1 ≤ 31 * N / 32 := by
    have h := mul_le_mul_of_nonneg_left hNceil (by norm_num : (0 : ℝ) ≤ 31 / 32)
    have h' : 31 / 32 * (32 * (Real.sqrt 2 * Rde + 1) / 31) = Real.sqrt 2 * Rde + 1 := by ring
    calc Real.sqrt 2 * Rde + 1 = 31 / 32 * (32 * (Real.sqrt 2 * Rde + 1) / 31) := h'.symm
      _ ≤ 31 / 32 * N := h
      _ = 31 * N / 32 := by ring
  have hNge : Real.sqrt 2 * Rde ≤ 31 * N / 32 := by linarith
  -- the geometric hypothesis, divided by 32
  have hYΞ : 17 * N / 16 + 1 + Real.sqrt 2 * Rde ≤ Y₀ - Ξ := by linarith [hgeo]
  have hY0pos : 0 < Y₀ := by linarith
  -- real part of the segment
  have hreA : 31 * N / 32 ≤ (z₁ + s • (z₂ - z₁)).re := by
    rw [seg_re_eq]
    have e1 := mul_le_mul_of_nonneg_left hre1 (by linarith : (0 : ℝ) ≤ 1 - s)
    have e2 := mul_le_mul_of_nonneg_left hre2 hs0
    linarith
  have hreB : (z₁ + s • (z₂ - z₁)).re ≤ 33 * N / 32 := by
    rw [seg_re_eq]
    have e1 := mul_le_mul_of_nonneg_left hre1' (by linarith : (0 : ℝ) ≤ 1 - s)
    have e2 := mul_le_mul_of_nonneg_left hre2' hs0
    linarith
  -- imaginary part of the segment against the weighted height
  have himbound : |(z₁ + s • (z₂ - z₁)).im - ((1 - s) * c₁ + s * c₂) * w.im| ≤ N / 32 := by
    rw [seg_im_eq]
    have e : (1 - s) * z₁.im + s * z₂.im - ((1 - s) * c₁ + s * c₂) * w.im
        = (1 - s) * (z₁.im - c₁ * w.im) + s * (z₂.im - c₂ * w.im) := by ring
    rw [e]
    calc |(1 - s) * (z₁.im - c₁ * w.im) + s * (z₂.im - c₂ * w.im)|
        ≤ |(1 - s) * (z₁.im - c₁ * w.im)| + |s * (z₂.im - c₂ * w.im)| := abs_add_le _ _
      _ = (1 - s) * |z₁.im - c₁ * w.im| + s * |z₂.im - c₂ * w.im| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s),
              abs_of_nonneg hs0]
      _ ≤ (1 - s) * (N / 32) + s * (N / 32) := by
            have a := mul_le_mul_of_nonneg_left him1 (by linarith : (0 : ℝ) ≤ 1 - s)
            have b := mul_le_mul_of_nonneg_left him2 hs0
            linarith
      _ = N / 32 := by ring
  have hcge : Y₀ ≤ (1 - s) * c₁ + s * c₂ := by
    have e1 := mul_le_mul_of_nonneg_left hY1 (by linarith : (0 : ℝ) ≤ 1 - s)
    have e2 := mul_le_mul_of_nonneg_left hY2 hs0
    linarith
  have hcoefpos : 0 < (1 - s) * c₁ + s * c₂ := lt_of_lt_of_le hY0pos hcge
  have habscoef : |(1 - s) * c₁ + s * c₂| = (1 - s) * c₁ + s * c₂ := abs_of_pos hcoefpos
  -- the height of the segment is at least `Y₀ - N/32`
  have hyge : Y₀ - N / 32 ≤ |(z₁ + s • (z₂ - z₁)).im| := by
    have hb : Y₀ ≤ |((1 - s) * c₁ + s * c₂) * w.im| := by
      rw [abs_mul, habscoef, hwim, mul_one]; exact hcge
    have htri := abs_sub_abs_le_abs_sub (((1 - s) * c₁ + s * c₂) * w.im)
        ((z₁ + s • (z₂ - z₁)).im)
    have h3 : |((1 - s) * c₁ + s * c₂) * w.im - (z₁ + s • (z₂ - z₁)).im| ≤ N / 32 := by
      rw [abs_sub_comm]; exact himbound
    linarith [htri, h3, hb]
  have hmA : Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α (z₁ + s • (z₂ - z₁)) := by
    have hCα' : (1 / α).re = Cα + Ξ := by linarith
    rw [Work.Pert.margA, hCα']
    have h1 := abs_nonneg ((z₁ + s • (z₂ - z₁)).im + (1 / α).im)
    linarith [hreA, le_of_lt hCα0, h1, hNge]
  have hmB : Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α (z₁ + s • (z₂ - z₁)) := by
    rw [Work.Pert.margB]
    linarith [hyge, hreB, hYΞ]
  exact le_min hmA hmB

end Work.Pert.PinLogDev
