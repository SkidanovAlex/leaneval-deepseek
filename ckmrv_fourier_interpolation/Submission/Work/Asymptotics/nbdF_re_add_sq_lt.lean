/-
# `Re z + d` is small when `γ • z` and `z` both lie in the thickening `nbdF`

Let `γ = [[a, b], [1, d]] ∈ SL(2, ℤ)` (bottom-left entry `1`) and suppose that both `z` and
`γ • z` lie in the `1/16`-thickening `nbdF` of `closure 𝓕` (CKMRV (3.13)).  Then

  `(Re z + d)² < 7/16`.

Since `det γ = 1` and `c = 1`, the fractional linear transformation is
`γ • z = a - 1/(z + d)`, so the denominator is `z + d`.  Writing `y = Im z` and
`v = Im (γ • z)`, the imaginary part identity `Im (γ • z) = y / ‖z + d‖²` gives

  `(Re z + d)² + y² = ‖z + d‖² = y / v`.

Both `y` and `v` exceed `3/4` because `z, γ • z ∈ nbdF`
(`Work.Asymptotics.im_gt_of_mem_nbdF`), so

  `(Re z + d)² = y/v - y² < (4/3) y - y² < 7/16`,

the last bound because `y ↦ (4/3) y - y²` is strictly decreasing on `y > 2/3` and equals
`7/16` at `y = 3/4` (indeed `(4/3) y - y² = 7/16 - (y - 3/4)(y - 7/12)`).
-/
import Mathlib
import Submission.Work.Asymptotics.DomainFThickening

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups

namespace Work.Asymptotics

/-- `‖z + D‖² = (Re z + D)² + (Im z)²` for `z ∈ ℍ` and a real number `D`. -/
lemma normSq_coe_add_ofReal (z : UpperHalfPlane) (D : ℝ) :
    ‖(z : ℂ) + (D : ℂ)‖ ^ 2 = (z.re + D) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The Möbius action of `γ ∈ SL(2, ℤ)` with bottom-left entry `1` has imaginary part

  `Im (γ • z) = Im z / ((Re z + d)² + (Im z)²)`,  where `d = γ 1 1`,

i.e. the denominator of the fractional linear transformation is `z + d` with `d` real. -/
lemma im_smul_eq_of_c_eq_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {z : UpperHalfPlane}
    (hc : γ 1 0 = 1) :
    (γ • z).im = z.im / ((z.re + ((γ 1 1 : ℤ) : ℝ)) ^ 2 + z.im ^ 2) := by
  have h : (γ • z).im = z.im / ‖((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ)‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, Complex.normSq_eq_norm_sq]
  rw [h, hc]
  simp only [Int.cast_one, one_mul]
  congr 1
  simpa using normSq_coe_add_ofReal z ((γ 1 1 : ℤ) : ℝ)

theorem nbdF_re_add_sq_lt {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {z : UpperHalfPlane}
    (hz : z ∈ Work.Asymptotics.nbdF) (hw : γ • z ∈ Work.Asymptotics.nbdF) (hc : γ 1 0 = 1) :
    (z.re + ((γ 1 1 : ℤ) : ℝ)) ^ 2 < 7 / 16 := by
  set D : ℝ := ((γ 1 1 : ℤ) : ℝ) with hD
  set y : ℝ := z.im with hy
  set v : ℝ := (γ • z).im with hv
  -- Both imaginary parts exceed `3/4` since both points lie in `nbdF`.
  have hy34 : (3 / 4 : ℝ) < y := by rw [hy]; exact im_gt_of_mem_nbdF hz
  have hv34 : (3 / 4 : ℝ) < v := by rw [hv]; exact im_gt_of_mem_nbdF hw
  -- The imaginary part identity for the action.
  have h1 : v = y / ((z.re + D) ^ 2 + y ^ 2) := by
    rw [hv, hy, hD]; exact im_smul_eq_of_c_eq_one hc
  have hy_pos : 0 < y := by linarith
  have hS_pos : 0 < (z.re + D) ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (z.re + D), sq_pos_of_pos hy_pos]
  -- Hence `((Re z + D)² + y²) * v = y`.
  have hmul : ((z.re + D) ^ 2 + y ^ 2) * v = y := by
    rw [h1]; field_simp
  -- Since `v > 3/4`, the denominator is `< 4y/3`.
  have hSlt : (z.re + D) ^ 2 + y ^ 2 < 4 * y / 3 := by
    have h' : ((z.re + D) ^ 2 + y ^ 2) * (3 / 4) < ((z.re + D) ^ 2 + y ^ 2) * v :=
      mul_lt_mul_of_pos_left (by linarith) hS_pos
    rw [hmul] at h'
    linarith
  -- `(4/3) y - y² < 7/16` because `y > 3/4 > 7/12`.
  have hquad : 0 < (y - 3 / 4) * (y - 7 / 12) := mul_pos (by linarith) (by linarith)
  nlinarith [hSlt, hquad]

end Work.Asymptotics
