/-
# A point of `W1`-shape (near `Re τ = 1`, above the thinness scale) lies in `U₀`

Every point `τ` of `W1` satisfies `3/4 < Re τ`, `|Re τ - 1| < thin (Im τ)` and (being inside one
of the window balls) `-1 < Re τ < 1`; see `Socket.W1_re_bounds`, `Socket.W1_thin` and
`Socket.W1`'s definition.  This file records that these three conditions alone already place `τ`
in the socket region `U₀`: they are the *shape* of a point of `W1`, and `U₀` is a neighbourhood
of the line `Re τ = 1` in that shape.

Writing `x = Re τ`, `y = Im τ` and `m = min (y²) 1` (so that `thin y = m/4`), the hypothesis
`|x - 1| < m/4` together with `x < 1` gives

  `x - 3/4 > (1 - m)/4 ≥ 0`,

and hence

  `‖τ - 3/4‖² = (x - 3/4)² + y² > ((1-m)/4)² + m = (1 + 14m + m²)/16 > 1/16`,

so `‖τ - 3/4‖ > 1/4`: the point clears the Farey disc about `3/4`.  This is the only disc that is
not cleared by the crude real-part bounds `x > 3/4`; the other three inequalities follow from
`x > 3/4` alone:

* `‖τ - 1/4‖ > 1/2` since `x - 1/4 > 1/2`;
* `‖τ + 1/4‖ > 1` since `x + 1/4 > 1`;
* `‖τ + 3/4‖ > 3/2` since `x + 3/4 > 3/2`.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.Region

noncomputable section

open UpperHalfPlane

namespace Work.CKFinal.Socket

/-! ## Squared distances to the four Farey centres -/

private lemma norm_sub_quarter_sq (x : ℍ) :
    ‖(x : ℂ) - (1 / 4 : ℂ)‖ ^ 2 = (x.re - 1 / 4) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma norm_add_quarter_sq (x : ℍ) :
    ‖(x : ℂ) + (1 / 4 : ℂ)‖ ^ 2 = (x.re + 1 / 4) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma norm_sub_threequarter_sq (x : ℍ) :
    ‖(x : ℂ) - (3 / 4 : ℂ)‖ ^ 2 = (x.re - 3 / 4) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma norm_add_threequarter_sq (x : ℍ) :
    ‖(x : ℂ) + (3 / 4 : ℂ)‖ ^ 2 = (x.re + 3 / 4) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

/-- From `(1/4)² < ‖w‖²` conclude `1/4 < ‖w‖`. -/
private lemma quarter_lt_norm {w : ℂ} (h : (1 / 4 : ℝ) ^ 2 < ‖w‖ ^ 2) : (1 : ℝ) / 4 < ‖w‖ := by
  have h' := sq_lt_sq.mp h
  simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), abs_of_nonneg (norm_nonneg w)] using h'

/-- **The shape of a point of `W1` meets `U₀`.**  A point `τ` with `3/4 < Re τ < 1` and
`|Re τ - 1| < thin (Im τ)` lies in the socket region `U₀`, i.e. strictly outside the four closed
Farey discs of radius `1/4` centred at `±1/4`, `±3/4`. -/
theorem mem_U0_of_W1_shape {τ : UpperHalfPlane} (hlo : 3 / 4 < τ.re) (hhi : τ.re < 1)
    (hthin : |τ.re - 1| < Work.CKFinal.Socket.thin τ.im) : τ ∈ Work.CKFinal.U0 := by
  rw [Work.CKFinal.mem_U0_iff]
  refine ⟨by linarith, hhi, ?_, ?_, ?_, ?_⟩
  · -- disc about `1/4`: `Re τ - 1/4 > 1/2`
    apply quarter_lt_norm
    rw [norm_sub_quarter_sq τ]
    nlinarith
  · -- disc about `-1/4`: `Re τ + 1/4 > 1`
    apply quarter_lt_norm
    rw [norm_add_quarter_sq τ]
    nlinarith
  · -- disc about `3/4`: the thinness hypothesis is used here
    apply quarter_lt_norm
    rw [norm_sub_threequarter_sq τ]
    set m := min (τ.im ^ 2) 1 with hm
    have hm_pos : 0 < m := by rw [hm]; exact lt_min (pow_pos τ.im_pos 2) one_pos
    have hm_le_one : m ≤ 1 := by rw [hm]; exact min_le_right _ _
    have hm_le : m ≤ τ.im ^ 2 := by rw [hm]; exact min_le_left _ _
    have hthin' : |τ.re - 1| < m / 4 := by
      rw [Work.CKFinal.Socket.thin, ← hm] at hthin
      exact hthin
    have hd : (1 - m) / 4 < τ.re - 3 / 4 := by
      have h2 := (abs_lt.mp hthin').1
      linarith
    have hdge : 0 ≤ (1 - m) / 4 := by linarith
    have hsq : ((1 - m) / 4) ^ 2 < (τ.re - 3 / 4) ^ 2 := by nlinarith
    nlinarith [hsq, hm_le, hm_pos]
  · -- disc about `-3/4`: `Re τ + 3/4 > 3/2`
    apply quarter_lt_norm
    rw [norm_add_threequarter_sq τ]
    nlinarith

end Work.CKFinal.Socket
