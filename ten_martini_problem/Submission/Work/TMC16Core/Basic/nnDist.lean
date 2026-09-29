import Mathlib
import Submission.Work.TMC16Core.Defs

/-!
# Distance to the nearest integer, and `S w = |sin (π w)|`

`nn x = ‖x‖_{ℝ/ℤ} = |x - round x|` is the distance from `x` to the nearest integer and
`S w = |sin (π w)|` is the corresponding trigonometric weight.  These are the quantities
appearing in the trigonometric product estimates of AJ §9: a block of multiples of `α` is well
separated exactly when the corresponding `nn` values are bounded below, and comparing the
products `|sin (2π (x + k p/(2q)))|` is comparing `S` of the corresponding arguments.
-/

noncomputable section

namespace Work.TMC16Core.Basic

/-- Distance to the nearest integer. -/
def nn (x : ℝ) : ℝ := |x - round x|

/-- `S w = |sin (π w)|`. -/
def S (w : ℝ) : ℝ := |Real.sin (Real.pi * w)|

lemma nn_eq_fracDist (x : ℝ) : nn x = Work.TMC16Core.fracDist x := rfl

lemma nn_nonneg (x : ℝ) : 0 ≤ nn x := abs_nonneg _

lemma nn_le_half (x : ℝ) : nn x ≤ 1 / 2 := abs_sub_round x

/-- `nn x ≤ |x|`: the distance to the nearest integer never exceeds the distance to `0`. -/
lemma nn_le_abs (x : ℝ) : nn x ≤ |x| := by
  simpa [nn] using round_le x 0

/-- `nn x ≤ |x - m|` for an integer `m`: `round x` is the nearest integer. -/
lemma nn_le_abs_sub_intCast (x : ℝ) (m : ℤ) : nn x ≤ |x - (m : ℝ)| := by
  simpa only [nn] using round_le x m

/-- The triangle inequality for the distance to the nearest integer. -/
lemma nn_add_le (x y : ℝ) : nn (x + y) ≤ nn x + nn y := by
  have h : nn (x + y) ≤ |x + y - (((round x : ℤ) + round y : ℤ) : ℝ)| :=
    nn_le_abs_sub_intCast _ _
  have h2 : x + y - (((round x : ℤ) + round y : ℤ) : ℝ)
      = (x - ((round x : ℤ) : ℝ)) + (y - ((round y : ℤ) : ℝ)) := by push_cast; ring
  rw [h2] at h
  calc nn (x + y)
      ≤ |(x - ((round x : ℤ) : ℝ)) + (y - ((round y : ℤ) : ℝ))| := h
    _ ≤ |x - ((round x : ℤ) : ℝ)| + |y - ((round y : ℤ) : ℝ)| := abs_add_le _ _
    _ = nn x + nn y := by rw [nn, nn]

/-- `nn` is 1-Lipschitz: `nn x ≤ nn y + |x - y|`. -/
lemma nn_sub_le_abs (x y : ℝ) : nn x ≤ nn y + |x - y| := by
  have h := nn_add_le (x - y) y
  rw [sub_add_cancel] at h
  have h2 := nn_le_abs (x - y)
  linarith

/-- `nn x = 0` exactly at the integers. -/
lemma nn_eq_zero_iff (x : ℝ) : nn x = 0 ↔ ∃ z : ℤ, x = (z : ℝ) := by
  rw [nn, abs_eq_zero, sub_eq_zero]
  constructor
  · intro h; exact ⟨round x, h⟩
  · rintro ⟨z, rfl⟩; exact_mod_cast (round_intCast z).symm

lemma nn_add_intCast (x : ℝ) (m : ℤ) : nn (x + (m : ℝ)) = nn x := by
  have h2 : x + (m : ℝ) - ((round (x + (m : ℝ)) : ℤ) : ℝ) = x - ((round x : ℤ) : ℝ) := by
    rw [round_add_intCast]
    push_cast
    ring
  simp only [nn, h2]

lemma nn_sub_intCast (x : ℝ) (m : ℤ) : nn (x - (m : ℝ)) = nn x := by
  have h := nn_add_intCast x (-m)
  simpa [sub_eq_add_neg] using h

lemma S_nonneg (w : ℝ) : 0 ≤ S w := abs_nonneg _

lemma S_add_intCast (w : ℝ) (m : ℤ) : S (w + (m : ℝ)) = S w := by
  have h : Real.pi * (w + (m : ℝ)) = Real.pi * w + (m : ℤ) * Real.pi := by push_cast; ring
  have h1 : |(-1 : ℝ) ^ m * Real.sin (Real.pi * w)| = |Real.sin (Real.pi * w)| := by
    rw [abs_mul]
    have : |(-1 : ℝ) ^ m| = 1 := by simp
    rw [this, one_mul]
  simpa only [S, h, Real.sin_add_int_mul_pi] using h1

/-- For `|w| ≤ 1/2`, `S w = sin (π |w|)`. -/
lemma S_eq_sin_abs (w : ℝ) (h : |w| ≤ 1 / 2) : S w = Real.sin (Real.pi * |w|) := by
  rw [S]
  have h1 : |Real.pi * w| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
    nlinarith [Real.pi_pos, h]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi h1, abs_mul, abs_of_nonneg Real.pi_pos.le]

/-- `S w = sin (π * nn w)`: `S` is determined by the distance of `w` to the nearest integer. -/
lemma S_eq_sin_nn (w : ℝ) : S w = Real.sin (Real.pi * nn w) := by
  have hd : |w - (round w : ℝ)| ≤ 1 / 2 := by
    simpa only [nn] using nn_le_half w
  have hsub : S w = S (w - (round w : ℝ)) := by
    have h := S_add_intCast (w - (round w : ℝ)) (round w)
    simpa using h
  rw [hsub, S_eq_sin_abs (w - (round w : ℝ)) hd]
  simp only [nn]

/-- Jordan's inequality in the form used for `S`: `(2/π) * (π * nn t) ≤ S t`, i.e.
`S t ≥ 2 * nn t`. -/
lemma two_div_pi_mul_le_S (t : ℝ) : 2 / Real.pi * (Real.pi * nn t) ≤ S t := by
  rw [S_eq_sin_nn]
  exact Real.mul_le_sin (by nlinarith [Real.pi_pos, nn_nonneg t]) (by nlinarith [Real.pi_pos, nn_le_half t])

/-- `S` is monotone in `nn`. -/
lemma S_mono_of_nn_le {a b : ℝ} (h : nn a ≤ nn b) : S a ≤ S b := by
  rw [S_eq_sin_nn, S_eq_sin_nn]
  refine Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos, nn_nonneg a])
    (by nlinarith [Real.pi_pos, nn_le_half b]) ?_
  nlinarith [Real.pi_pos, h]

/-- The other half of Jordan's inequality for `S`: `S w ≤ π * nn w`. -/
lemma S_le_pi_mul_nn (w : ℝ) : S w ≤ Real.pi * nn w := by
  rw [S_eq_sin_nn]
  exact Real.sin_le (by nlinarith [Real.pi_pos, nn_nonneg w])

end Work.TMC16Core.Basic
