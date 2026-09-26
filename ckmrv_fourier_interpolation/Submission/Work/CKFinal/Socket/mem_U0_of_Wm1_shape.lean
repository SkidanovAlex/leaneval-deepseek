/-
# A point of `Wm1`-shape (near `Re τ = -1`, above the thinness scale) lies in `U₀`

Every point `τ` of `Wm1` satisfies `-1 < Re τ`, `Re τ < -3/4`, `|Re τ + 1| < thin (Im τ)` and (being
translated by `+1` into `U₀`) `Re τ < -3/4`; see `Socket.Wm1_re_bounds` and `Socket.Wm1`'s
definition.  This file records that these three conditions alone already place `τ` in the socket
region `U₀`: they are the *shape* of a point of `Wm1`, and `U₀` is a neighbourhood of the line
`Re τ = -1` in that shape.

Writing `x = Re τ`, `y = Im τ`, `t = x + 1` and `m = min (y²) 1` (so that `thin y = m/4`), the
hypothesis `|t| < m/4` together with `x > -1` gives `0 < t < m/4`, hence, since `m ≤ y²`,

  `t/2 < y²`,

and then

  `‖τ + 3/4‖² = (x + 3/4)² + y² = (1/4 - t)² + y² = 1/16 - t/2 + t² + y² > 1/16`,

so `‖τ + 3/4‖ > 1/4`: the point clears the Farey disc about `-3/4`.  This is the only disc that is
not cleared by the crude real-part bound `x < -3/4`; the other three inequalities follow from it
alone:

* `‖τ - 1/4‖ > 1` since `x - 1/4 < -1`;
* `‖τ + 1/4‖ > 1/2` since `x + 1/4 < -1/2`;
* `‖τ - 3/4‖ > 3/2` since `x - 3/4 < -3/2`.
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

/-- If `u < -c` with `c > 0` then `c² < u²`. -/
private lemma sq_gt_sq_of_lt_neg {u c : ℝ} (hc : 0 < c) (h : u < -c) : c ^ 2 < u ^ 2 := by
  have h1 : 0 < -(u + c) := by linarith
  have h2 : 0 < c - u := by linarith
  have h3 := mul_pos h2 h1
  nlinarith [h3]

/-- **The shape of a point of `Wm1` meets `U₀`.**  A point `τ` with `-1 < Re τ < -3/4` and
`|Re τ + 1| < thin (Im τ)` lies in the socket region `U₀`, i.e. strictly outside the four closed
Farey discs of radius `1/4` centred at `±1/4`, `±3/4`. -/
theorem mem_U0_of_Wm1_shape {τ : UpperHalfPlane} (hlo : -1 < τ.re) (hhi : τ.re < -3 / 4)
    (hthin : |τ.re + 1| < Work.CKFinal.Socket.thin τ.im) : τ ∈ Work.CKFinal.U0 := by
  rw [Work.CKFinal.mem_U0_iff]
  refine ⟨hlo, by linarith, ?_, ?_, ?_, ?_⟩
  · -- disc about `1/4`: `Re τ - 1/4 < -1`
    apply quarter_lt_norm
    rw [norm_sub_quarter_sq τ]
    have h1 : (1 : ℝ) ^ 2 < (τ.re - 1 / 4) ^ 2 :=
      sq_gt_sq_of_lt_neg (u := τ.re - 1 / 4) (c := 1) (by norm_num) (by linarith)
    nlinarith [sq_nonneg τ.im]
  · -- disc about `-1/4`: `Re τ + 1/4 < -1/2`
    apply quarter_lt_norm
    rw [norm_add_quarter_sq τ]
    have h1 : (1 / 2 : ℝ) ^ 2 < (τ.re + 1 / 4) ^ 2 :=
      sq_gt_sq_of_lt_neg (u := τ.re + 1 / 4) (c := 1 / 2) (by norm_num) (by linarith)
    nlinarith [sq_nonneg τ.im]
  · -- disc about `3/4`: `Re τ - 3/4 < -3/2`
    apply quarter_lt_norm
    rw [norm_sub_threequarter_sq τ]
    have h1 : (3 / 2 : ℝ) ^ 2 < (τ.re - 3 / 4) ^ 2 :=
      sq_gt_sq_of_lt_neg (u := τ.re - 3 / 4) (c := 3 / 2) (by norm_num) (by linarith)
    nlinarith [sq_nonneg τ.im]
  · -- disc about `-3/4`: the thinness hypothesis is used here
    apply quarter_lt_norm
    rw [norm_add_threequarter_sq τ]
    have hthin' : |τ.re + 1| < min (τ.im ^ 2) 1 / 4 := by
      rw [Work.CKFinal.Socket.thin] at hthin
      exact hthin
    set t : ℝ := τ.re + 1 with ht
    have ht_lt : t < min (τ.im ^ 2) 1 / 4 := by
      rw [ht]
      exact (abs_lt.mp hthin').2
    have hkey : t / 2 < τ.im ^ 2 := by
      have hm : min (τ.im ^ 2) 1 ≤ τ.im ^ 2 := min_le_left _ _
      nlinarith [ht_lt, hm, sq_nonneg τ.im]
    have hEq : (τ.re + 3 / 4) ^ 2 = ((1 : ℝ) / 4 - t) ^ 2 := by
      rw [ht]; ring
    rw [hEq]
    nlinarith [hkey, sq_nonneg t]

end Work.CKFinal.Socket
