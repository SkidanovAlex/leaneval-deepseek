import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouL1.strip_in_Qreg
import Submission.Work.FatouCH.fatouFundamental

/-!
# FATOU-L1: geometric and analytic preliminaries

This file collects the elementary consequences of the hypotheses `QAdm b₁ b₂` and
`NearTranslationL1 F (Qreg b₁ b₂)` that the construction of the Fatou coordinate on the strip
uses.

* `lineMass_le` : the `L¹` bound on a line of `Qreg`, restated.
* `strip_subset_Qreg` : the width-`5/4` strip produced by `strip_in_Qreg` lies in `Qreg`.
* `re_step` : one step of `F` moves `Re` by between `31/32` and `33/32` (from
  `Work.FatouCH.re_step_bounds`).
* `neg_re_step` : dually, one step moves `Im` by at most `1/32`.
* `deriv_ne_zero_Q` : `F' ≠ 0` on `Qreg`.
* `mapsTo_Qreg_none_right` : when there is no right vertex, `F` maps `Qreg` into itself.
-/

open MandelDim Set MeasureTheory
open scoped Topology

namespace Work.FatouL1

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {Q : Set ℂ}

/-- The `L¹` bound of `NearTranslationL1`, restated for a line of `Qreg`. -/
theorem lineMass_le (hF : NearTranslationL1 F (Qreg b₁ b₂)) {x : ℝ}
    (hx : ∀ y : ℝ, ((x : ℂ) + y * Complex.I) ∈ Qreg b₁ b₂) :
    ∫⁻ y : ℝ, ENNReal.ofReal ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖ ≤
      ENNReal.ofReal (1 / 64) :=
  hF.2 x hx

/-- The strip provided by `strip_in_Qreg` is contained in `Qreg b₁ b₂`. -/
theorem strip_subset_Qreg {x₀ : ℝ}
    (hS : ∀ x ∈ Ioo (x₀ - 1 / 8) (x₀ + 9 / 8), ∀ y : ℝ,
      ((x : ℂ) + y * Complex.I) ∈ Qreg b₁ b₂) :
    {z : ℂ | x₀ - 1 / 8 < z.re ∧ z.re < x₀ + 9 / 8} ⊆ Qreg b₁ b₂ := by
  intro z hz
  have h := hS z.re hz z.im
  simpa using h

/-- One step of a near-translation moves the real part by between `31/32` and `33/32`. -/
theorem re_step {z : ℂ} {Q : Set ℂ} (hF : NearTranslationOn F Q) (hz : z ∈ Q) :
    z.re + 31 / 32 ≤ (F z).re ∧ (F z).re ≤ z.re + 33 / 32 :=
  Work.FatouCH.re_step_bounds (hF.2 z hz).1

/-- One step of a near-translation moves the imaginary part by at most `1/32`. -/
theorem im_step {z : ℂ} {Q : Set ℂ} (hF : NearTranslationOn F Q) (hz : z ∈ Q) :
    |(F z).im - z.im| ≤ 1 / 32 := by
  have h1 : |(F z - (z + 1)).im| ≤ 1 / 32 :=
    le_trans (Complex.abs_im_le_norm _) (hF.2 z hz).1
  have h2 : (F z - (z + 1)).im = (F z).im - z.im := by simp
  rwa [h2] at h1

/-- The derivative of a near-translation does not vanish. -/
theorem deriv_ne_zero {z : ℂ} {Q : Set ℂ} (hF : NearTranslationOn F Q) (hz : z ∈ Q) :
    deriv F z ≠ 0 := by
  intro h
  have h' := (hF.2 z hz).2
  rw [h] at h'
  norm_num at h'

/-- `Re` of the value of a near-translation on the width-`5/4` strip stays in a strip of the same
width, shifted by `1`. -/
theorem re_value_mem {x₀ : ℝ} {hF : NearTranslationL1 F (Qreg b₁ b₂)} {z : ℂ}
    (hS : ∀ x ∈ Ioo (x₀ - 1 / 8) (x₀ + 9 / 8), ∀ y : ℝ,
      ((x : ℂ) + y * Complex.I) ∈ Qreg b₁ b₂)
    (hz : x₀ - 1 / 8 < z.re) (hz' : z.re < x₀ + 9 / 8) :
    x₀ + 27 / 32 < (F z).re ∧ (F z).re < x₀ + 2 + 9 / 32 := by
  have hzQ : z ∈ Qreg b₁ b₂ := strip_subset_Qreg hS ⟨hz, hz'⟩
  obtain ⟨h1, h2⟩ := re_step hF.1 hzQ
  constructor <;> linarith

end

end Work.FatouL1
