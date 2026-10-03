import Mathlib
import Submission.Work.Motion.disc_autom

/-!
# The derivative of the disc automorphism `mob a` at `a` and at `0`

`Work.Motion.mob a t = (t - a) / (1 - conj a * t)` is the Möbius transformation of the unit
disc sending `a` to `0`.  Here we compute its complex derivative

`deriv (mob a) t = (1 - conj a * a) / (1 - conj a * t)^2`

wherever the denominator does not vanish, and deduce the two values used in the Schwarz–Pick
estimate of the moving IFS: `‖deriv (mob a) a‖ = (1 - ‖a‖^2)⁻¹` and
`‖deriv (mob a) 0‖ = 1 - ‖a‖^2` for `‖a‖ < 1`.
-/

namespace Work.Motion

open scoped ComplexConjugate

/-- The complex derivative of `mob a` at a point where the denominator `1 - conj a * t` does not
vanish. -/
theorem deriv_mob {a t : ℂ} (h : 1 - conj a * t ≠ 0) :
    deriv (mob a) t = (1 - conj a * a) / (1 - conj a * t) ^ 2 := by
  have h1 : HasDerivAt (fun s : ℂ => s - a) 1 t := by
    simpa using (hasDerivAt_id t).sub_const a
  have h2' : HasDerivAt (fun s : ℂ => conj a * s) (conj a) t := by
    simpa using (hasDerivAt_id t).const_mul (conj a)
  have h2 : HasDerivAt (fun s : ℂ => 1 - conj a * s) (-(conj a)) t := by
    simpa using h2'.const_sub (1 : ℂ)
  have h3 := h1.div h2 h
  have heq : (1 * (1 - conj a * t) - (t - a) * (-(conj a))) = 1 - conj a * a := by ring
  rw [heq] at h3
  exact h3.deriv

theorem norm_deriv_mob {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv (mob a) a‖ = (1 - ‖a‖ ^ 2)⁻¹ ∧
    ‖deriv (mob a) 0‖ = 1 - ‖a‖ ^ 2 := by
  have hr1 : ‖a‖ ^ 2 < 1 := by nlinarith [norm_nonneg a, ha]
  have hcast : conj a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; norm_num
  have hnorm_a : ‖(1 : ℂ) - conj a * a‖ = 1 - ‖a‖ ^ 2 := by
    have h : (1 : ℂ) - conj a * a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [hcast]; push_cast; ring
    rw [h, show ‖(((1 - ‖a‖ ^ 2 : ℝ)) : ℂ)‖ = |(1 - ‖a‖ ^ 2 : ℝ)| from RCLike.norm_ofReal _,
      abs_of_nonneg (by linarith)]
  have hne_a : 1 - conj a * a ≠ 0 := by
    intro hz
    have := hnorm_a
    rw [hz, norm_zero] at this
    linarith
  have hne_0 : 1 - conj a * 0 ≠ 0 := by norm_num
  constructor
  · have hda : deriv (mob a) a = (1 - conj a * a)⁻¹ := by
      rw [deriv_mob hne_a]; field_simp
    rw [hda, norm_inv, hnorm_a]
  · have hd0 : deriv (mob a) 0 = 1 - conj a * a := by
      rw [deriv_mob hne_0]; norm_num
    rw [hd0, hnorm_a]

end Work.Motion
