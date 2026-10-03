/-
# `Submission.Work.FIArea3.polarBoxCardLeOne` — the polar box is a single point when `θ√N < 1/10`

The polar box (5.14) is contained in a disc of radius `5θ√N` (`Work.FIArea4.dist_polarBox_le`).
Two distinct Gaussian integers are at distance at least `1` in `ℂ` (their real or imaginary parts
differ by an integer of modulus `≥ 1`), so once `5θ√N < 1/2` the disc of radius `5θ√N` contains at
most one Gaussian integer: any two elements `z ≠ w` of the box would give
`‖z - w‖ ≤ 2·5θ√N < 1`, a contradiction with `‖z - w‖ ≥ 1`.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea4.polarBox_card_le

namespace Work.FIArea3

open scoped BigOperators
open scoped Classical

noncomputable section

/-- **Separation of Gaussian integers.**  If `‖z - w‖ < 1` in `ℂ` for two Gaussian integers, then
`z = w`: otherwise the real (or imaginary) parts differ by a nonzero integer, so by at least `1`
in absolute value, and `|Re ζ| ≤ ‖ζ‖`. -/
lemma eq_of_norm_toComplex_sub_lt_one {z w : GaussianInt}
    (h : ‖z.toComplex - w.toComplex‖ < 1) : z = w := by
  apply Zsqrtd.ext
  · have h1 : |(z.toComplex - w.toComplex).re| < 1 :=
      lt_of_le_of_lt (Complex.abs_re_le_norm _) h
    rw [Complex.sub_re] at h1
    rw [← GaussianInt.intCast_re z, ← GaussianInt.intCast_re w] at h1
    have h2 : ((|(z.re - w.re : ℤ)| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs, Int.cast_sub]; exact h1
    exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp (by exact_mod_cast h2))
  · have h1 : |(z.toComplex - w.toComplex).im| < 1 :=
      lt_of_le_of_lt (Complex.abs_im_le_norm _) h
    rw [Complex.sub_im] at h1
    rw [← GaussianInt.intCast_im z, ← GaussianInt.intCast_im w] at h1
    have h2 : ((|(z.im - w.im : ℤ)| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs, Int.cast_sub]; exact h1
    exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp (by exact_mod_cast h2))

/-- **The polar box (5.14) is a single point when `θ√N < 1/10`.**  The box lies in a disc of radius
`5θ√N < 1/2`, and a disc of radius `< 1/2` contains at most one Gaussian integer. -/
lemma polarBoxCardLeOne (Pa : Work.FITop.Params) (φ : ℝ)
    (h : Pa.θ * Real.sqrt Pa.N < 1 / 10) :
    (Work.FIArea3.polarBoxFinset Pa φ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz w hw
  rw [mem_polarBoxFinset] at hz hw
  obtain ⟨-, hzbox⟩ := hz
  obtain ⟨-, hwbox⟩ := hw
  have hzdist := Work.FIArea4.dist_polarBox_le Pa φ z hzbox
  have hwdist := Work.FIArea4.dist_polarBox_le Pa φ w hwbox
  apply eq_of_norm_toComplex_sub_lt_one
  set c : ℂ := (Real.sqrt Pa.N : ℂ)
      * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hc
  have hρ : 5 * Pa.θ * Real.sqrt Pa.N < 1 / 2 := by
    have h5 : 5 * (Pa.θ * Real.sqrt Pa.N) < 5 * (1 / 10) :=
      mul_lt_mul_of_pos_left h (by norm_num)
    linarith
  have hz' : ‖z.toComplex - c‖ ≤ 5 * Pa.θ * Real.sqrt Pa.N := by rw [hc]; exact hzdist
  have hw' : ‖w.toComplex - c‖ ≤ 5 * Pa.θ * Real.sqrt Pa.N := by rw [hc]; exact hwdist
  calc ‖z.toComplex - w.toComplex‖
      = ‖(z.toComplex - c) - (w.toComplex - c)‖ := by congr 1; ring
    _ ≤ ‖z.toComplex - c‖ + ‖w.toComplex - c‖ := norm_sub_le _ _
    _ < 1 := by linarith

end

end Work.FIArea3
