import Mathlib
import Submission.Work.Cert.Spec

namespace Work.Cert.ACGeom

open Work.Cert

/-- Rounding error of floor-division by `2`: for every integer `a`,
`|a/2 - a/2| ≤ 1/2` in `ℝ` (the integer quotient is `Int.ediv`). -/
lemma ediv_two_close (a : ℤ) : |((a / 2 : ℤ) : ℝ) - (a : ℝ) / 2| ≤ 1 / 2 := by
  have h := Int.mul_ediv_add_emod a 2
  have hcast : (2 : ℝ) * ((a / 2 : ℤ) : ℝ) = (a : ℝ) - ((a % 2 : ℤ) : ℝ) := by
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    linarith [h']
  have key : ((a / 2 : ℤ) : ℝ) - (a : ℝ) / 2 = -(((a % 2 : ℤ) : ℝ)) / 2 := by linarith [hcast]
  rcases Int.emod_two_eq_zero_or_one a with h0 | h1
  · have : ((a % 2 : ℤ) : ℝ) = 0 := by rw [h0]; norm_num
    rw [key, this]; norm_num
  · have : ((a % 2 : ℤ) : ℝ) = 1 := by rw [h1]; norm_num
    rw [key, this]; norm_num

/-- The centre of a leaf (`leafC`, the rounded midpoint of `A` and `B` at scale `S`) is within
`1/S` of the exact midpoint of the two endpoints. -/
theorem leafC_close (L : Leaf) : ‖leafC L - (cx L.Ax L.Ay + cx L.Bx L.By) / 2‖ ≤ 1 / (S : ℝ) := by
  have hS : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  set z := leafC L - (cx L.Ax L.Ay + cx L.Bx L.By) / 2 with hz
  have hre : |z.re| ≤ 1 / (2 * (S : ℝ)) := by
    have h1 : z.re = (leafCx L : ℝ) / (S : ℝ) - ((L.Ax : ℝ) + (L.Bx : ℝ)) / (2 * (S : ℝ)) := by
      rw [hz]
      simp only [leafC, cx, Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
      ring
    rw [h1]
    have hkey : |(leafCx L : ℝ) - ((L.Ax : ℝ) + (L.Bx : ℝ)) / 2| ≤ 1 / 2 := by
      have hcx : (leafCx L : ℝ) = ((L.Ax + L.Bx) / 2 : ℤ) := by rw [leafCx, fdiv]; rfl
      rw [hcx]
      simpa using ediv_two_close (L.Ax + L.Bx)
    have h1b : (leafCx L : ℝ) / (S : ℝ) - ((L.Ax : ℝ) + (L.Bx : ℝ)) / (2 * (S : ℝ))
        = ((leafCx L : ℝ) - ((L.Ax : ℝ) + (L.Bx : ℝ)) / 2) / (S : ℝ) := by ring_nf
    rw [h1b, abs_div, abs_of_pos hS]
    calc |(leafCx L : ℝ) - ((L.Ax : ℝ) + (L.Bx : ℝ)) / 2| / (S : ℝ)
        ≤ (1 / 2) / (S : ℝ) := div_le_div_of_nonneg_right hkey (le_of_lt hS)
      _ = 1 / (2 * (S : ℝ)) := by ring
  have him : |z.im| ≤ 1 / (2 * (S : ℝ)) := by
    have h1 : z.im = (leafCy L : ℝ) / (S : ℝ) - ((L.Ay : ℝ) + (L.By : ℝ)) / (2 * (S : ℝ)) := by
      rw [hz]
      simp only [leafC, cx, Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, add_zero,
        mul_one, zero_add]
      ring
    rw [h1]
    have hkey : |(leafCy L : ℝ) - ((L.Ay : ℝ) + (L.By : ℝ)) / 2| ≤ 1 / 2 := by
      have hcy : (leafCy L : ℝ) = ((L.Ay + L.By) / 2 : ℤ) := by rw [leafCy, fdiv]; rfl
      rw [hcy]
      simpa using ediv_two_close (L.Ay + L.By)
    have h1b : (leafCy L : ℝ) / (S : ℝ) - ((L.Ay : ℝ) + (L.By : ℝ)) / (2 * (S : ℝ))
        = ((leafCy L : ℝ) - ((L.Ay : ℝ) + (L.By : ℝ)) / 2) / (S : ℝ) := by ring_nf
    rw [h1b, abs_div, abs_of_pos hS]
    calc |(leafCy L : ℝ) - ((L.Ay : ℝ) + (L.By : ℝ)) / 2| / (S : ℝ)
        ≤ (1 / 2) / (S : ℝ) := div_le_div_of_nonneg_right hkey (le_of_lt hS)
      _ = 1 / (2 * (S : ℝ)) := by ring
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 1 / (2 * S) + 1 / (2 * S) := by linarith
    _ = 1 / S := by ring_nf

end Work.Cert.ACGeom
