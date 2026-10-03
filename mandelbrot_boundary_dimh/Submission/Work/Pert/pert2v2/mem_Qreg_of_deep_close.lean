import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# A point close to `u + A` with `‖A‖ ≤ c - 1` lies in `𝒬(-∞, -Ξ)` when `2c + Ξ < -u.re + |u.im|`

`MandelDim.Qreg none (some (-(Ξ : ℂ)))` is the region on the right of the vertex `-Ξ`, i.e.
`{z | z.re + Ξ < |z.im|}`.

The arithmetic content: `z` is within distance `1` of `u + A`, so
`z.re < (u + A).re + 1` and `|z.im| > |(u + A).im| - 1`.  Writing `‖A‖ ≤ c - 1`,
`(u + A).re ≤ u.re + c - 1` and `|(u + A).im| ≥ |u.im| - c`, the hypothesis
`2c + Ξ < -u.re + |u.im|` gives exactly

`z.re + Ξ < (u + A).re + 1 + Ξ ≤ u.re + c + Ξ < |u.im| - c ≤ |(u + A).im| - 1 < |z.im|`.
-/

namespace Work.Pert.pert2v2

theorem mem_Qreg_of_deep_close {z u A : ℂ} {Ξ c : ℝ}
    (hclose : ‖z - (u + A)‖ < 1) (hA : ‖A‖ + 1 ≤ c)
    (harith : 2 * c + Ξ < -u.re + |u.im|) :
    z ∈ MandelDim.Qreg none (some (-(Ξ : ℂ))) := by
  rw [show z ∈ MandelDim.Qreg none (some (-(Ξ : ℂ))) ↔ z.re + Ξ < |z.im| by
    simp [MandelDim.Qreg]]
  -- `z` is within distance `1` of `u + A`: real parts and imaginary parts are both close.
  have hzre : z.re < (u + A).re + 1 := by
    have h := Complex.abs_re_le_norm (z - (u + A))
    rw [Complex.sub_re] at h
    linarith [(abs_lt.mp (lt_of_le_of_lt h hclose)).2]
  have hzim : |(u + A).im| - 1 < |z.im| := by
    have h := Complex.abs_im_le_norm (z - (u + A))
    rw [Complex.sub_im] at h
    have hlt : |(u + A).im - z.im| < 1 := by
      rw [abs_sub_comm]; exact lt_of_le_of_lt h hclose
    have h2 : |(u + A).im| - |z.im| ≤ |(u + A).im - z.im| := by
      have := abs_abs_sub_abs_le_abs_sub (u + A).im z.im
      linarith [(abs_le.mp this).2]
    linarith
  -- `‖A‖ ≤ c - 1` bounds the real part of `u + A` from above and its imaginary part from below.
  have hAabs : ‖A‖ ≤ c - 1 := by linarith
  have hreA : (u + A).re ≤ u.re + c - 1 := by
    have := Complex.re_le_norm A
    rw [Complex.add_re]
    linarith
  have himA : |u.im| - c ≤ |(u + A).im| - 1 := by
    have h1 : |u.im| ≤ |(u + A).im| + |A.im| := by
      have h := abs_add_le ((u + A).im) (-(A.im))
      have h' : |(u + A).im - A.im| ≤ |(u + A).im| + |A.im| := by simpa using h
      rw [show (u + A).im - A.im = u.im by simp [Complex.add_im]] at h'
      exact h'
    have h2 : |A.im| ≤ c - 1 := le_trans (Complex.abs_im_le_norm A) hAabs
    linarith
  -- the arithmetic hypothesis, rearranged.
  have harith' : u.re + c + Ξ < |u.im| - c := by linarith
  linarith

end Work.Pert.pert2v2
