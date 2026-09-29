import Mathlib
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC7Core.Cocycle

/-!
# The spectral radius of the roots of `X² − τX + 1`

If `la, mu : ℂ` satisfy `la + mu = τ` (with `τ : ℝ`) and `la * mu = 1`, then they are the
roots of `X² − τX + 1`.  Their norms are `1` in the elliptic regime `|τ| ≤ 2` and
`(|τ| ± √(τ²−4))/2` in the hyperbolic regime, so the maximum of the two norms is exactly
`Work.TMC7Core.rhoSL τ`.
-/

namespace Work.TMC7Core.Solutions

/-- For reals with nonnegative product, `|x| + |y| = |x + y|`. -/
lemma abs_add_of_mul_nonneg (x y : ℝ) (h : 0 ≤ x * y) : |x| + |y| = |x + y| :=
  ((abs_add_eq_add_abs_iff x y).mpr (mul_nonneg_iff.mp h)).symm

/-- For reals with nonpositive product, `|x| + |y| = |x - y|`. -/
lemma abs_add_of_mul_nonpos (x y : ℝ) (h : x * y ≤ 0) : |x| + |y| = |x - y| := by
  have h2 : 0 ≤ x * (-y) := by nlinarith
  have := abs_add_of_mul_nonneg x (-y) h2
  simpa [abs_neg, sub_eq_add_neg] using this

/-- The elementary identity `2 * max |u| |v| = |u + v| + |u - v|` for real numbers. -/
lemma max_abs_identity (u v : ℝ) : max |u| |v| = (|u + v| + |u - v|) / 2 := by
  rcases le_total (|u|) (|v|) with h | h
  · rw [max_eq_right h]
    have hp : (u + v) * (u - v) ≤ 0 := by
      have hs : u ^ 2 ≤ v ^ 2 := (sq_le_sq).mpr h
      nlinarith [hs]
    rw [abs_add_of_mul_nonpos _ _ hp]
    rw [show (u + v) - (u - v) = 2 * v by ring, abs_mul]
    norm_num
  · rw [max_eq_left h]
    have hp : 0 ≤ (u + v) * (u - v) := by
      have hs : v ^ 2 ≤ u ^ 2 := (sq_le_sq).mpr h
      nlinarith [hs]
    rw [abs_add_of_mul_nonneg _ _ hp]
    rw [show (u + v) + (u - v) = 2 * u by ring, abs_mul]
    norm_num

/-- In the hyperbolic regime the two real roots `(τ ± s)/2` have maximum absolute value
`(|τ| + s)/2`. -/
lemma real_case (τ s : ℝ) (hs : 0 ≤ s) : max |(τ + s) / 2| |(τ - s) / 2| = (|τ| + s) / 2 := by
  rw [max_abs_identity]
  have e1 : (τ + s) / 2 + (τ - s) / 2 = τ := by ring
  have e2 : (τ + s) / 2 - (τ - s) / 2 = s := by ring
  rw [e1, e2, abs_of_nonneg hs]

/-- The norm of a real cast. -/
lemma norm_ofReal_cast (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by simp

/-- Norm of a halved complex number. -/
lemma norm_div_two (z : ℂ) : ‖z / 2‖ = ‖z‖ / 2 := by rw [norm_div]; norm_num

/-- Squared norm of `t + i c` for real `t, c`. -/
lemma norm_add_I_mul_sq (t c : ℝ) : ‖((t : ℂ) + Complex.I * (c : ℂ))‖ ^ 2 = t ^ 2 + c ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- Squared norm of `t - i c` for real `t, c`. -/
lemma norm_sub_I_mul_sq (t c : ℝ) : ‖((t : ℂ) - Complex.I * (c : ℂ))‖ ^ 2 = t ^ 2 + c ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

set_option maxHeartbeats 800000 in
/-- The two roots `la, mu` of `X² − τX + 1` (with `τ` real) have `max ‖la‖ ‖mu‖ = rhoSL τ`. -/
theorem max_norm_roots_eq_rhoSL (τ : ℝ) {la mu : ℂ} (hsum : la + mu = (τ : ℂ))
    (hprod : la * mu = 1) : max ‖la‖ ‖mu‖ = Work.TMC7Core.rhoSL τ := by
  have hz : (la - mu) ^ 2 = ((τ ^ 2 - 4 : ℝ) : ℂ) := by
    have h : (la - mu) ^ 2 = (la + mu) ^ 2 - 4 * (la * mu) := by ring
    rw [h, hsum, hprod]; push_cast; ring
  have hla : la = ((τ : ℂ) + (la - mu)) / 2 := by
    have h : la = ((la + mu) + (la - mu)) / 2 := by ring
    rw [hsum] at h; exact h
  have hmu : mu = ((τ : ℂ) - (la - mu)) / 2 := by
    have h : mu = ((la + mu) - (la - mu)) / 2 := by ring
    rw [hsum] at h; exact h
  rcases le_or_gt (2 : ℝ) |τ| with h2 | h2
  · -- hyperbolic regime: `2 ≤ |τ|`
    have hD : 0 ≤ τ ^ 2 - 4 := by nlinarith [sq_abs τ, abs_nonneg τ]
    set s : ℝ := Real.sqrt (τ ^ 2 - 4) with hsdef
    have hsnn : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
    have hs : (s : ℂ) ^ 2 = ((τ ^ 2 - 4 : ℝ) : ℂ) := by
      rw [hsdef, ← Complex.ofReal_pow, Real.sq_sqrt hD]
    have hcase : la - mu = (s : ℂ) ∨ la - mu = -(s : ℂ) :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans hs.symm)
    rcases hcase with hc | hc
    · have hA : la = (((τ + s) / 2 : ℝ) : ℂ) := by rw [hla, hc]; push_cast; ring
      have hB : mu = (((τ - s) / 2 : ℝ) : ℂ) := by rw [hmu, hc]; push_cast; ring
      rw [hA, hB, norm_ofReal_cast, norm_ofReal_cast, real_case τ s hsnn,
          Work.TMC7Core.rhoSL, if_pos h2, ← hsdef]
    · have hA : la = (((τ - s) / 2 : ℝ) : ℂ) := by rw [hla, hc]; push_cast; ring
      have hB : mu = (((τ + s) / 2 : ℝ) : ℂ) := by rw [hmu, hc]; push_cast; ring
      rw [hA, hB, norm_ofReal_cast, norm_ofReal_cast, max_comm, real_case τ s hsnn,
          Work.TMC7Core.rhoSL, if_pos h2, ← hsdef]
  · -- elliptic regime: `|τ| < 2`
    have hD : 0 ≤ 4 - τ ^ 2 := by nlinarith [sq_abs τ, abs_nonneg τ]
    set c : ℝ := Real.sqrt (4 - τ ^ 2) with hcdef
    have hc2 : c ^ 2 = 4 - τ ^ 2 := by rw [hcdef]; exact Real.sq_sqrt hD
    have hsc : (Complex.I * (c : ℂ)) ^ 2 = ((τ ^ 2 - 4 : ℝ) : ℂ) := by
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hc2]
      push_cast; ring
    have hcase : la - mu = Complex.I * (c : ℂ) ∨ la - mu = -(Complex.I * (c : ℂ)) :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans hsc.symm)
    have hnadd : ‖((τ : ℂ) + Complex.I * (c : ℂ))‖ = 2 := by
      have hnn := norm_nonneg ((τ : ℂ) + Complex.I * (c : ℂ))
      have hsq := norm_add_I_mul_sq τ c
      have hsqrt : ‖((τ : ℂ) + Complex.I * (c : ℂ))‖
          = Real.sqrt (‖((τ : ℂ) + Complex.I * (c : ℂ))‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]
      rw [hsqrt, hsq, show τ ^ 2 + c ^ 2 = 4 by linarith]
      norm_num
    have hnsub : ‖((τ : ℂ) - Complex.I * (c : ℂ))‖ = 2 := by
      have hnn := norm_nonneg ((τ : ℂ) - Complex.I * (c : ℂ))
      have hsq := norm_sub_I_mul_sq τ c
      have hsqrt : ‖((τ : ℂ) - Complex.I * (c : ℂ))‖
          = Real.sqrt (‖((τ : ℂ) - Complex.I * (c : ℂ))‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]
      rw [hsqrt, hsq, show τ ^ 2 + c ^ 2 = 4 by linarith]
      norm_num
    rw [Work.TMC7Core.rhoSL, if_neg (not_le.mpr h2)]
    rcases hcase with hc | hc
    · have hA : la = ((τ : ℂ) + Complex.I * (c : ℂ)) / 2 := by rw [hla, hc]
      have hB : mu = ((τ : ℂ) - Complex.I * (c : ℂ)) / 2 := by rw [hmu, hc]
      rw [hA, hB, norm_div_two, norm_div_two, hnadd, hnsub]
      norm_num
    · have hA : la = ((τ : ℂ) - Complex.I * (c : ℂ)) / 2 := by rw [hla, hc]; ring
      have hB : mu = ((τ : ℂ) + Complex.I * (c : ℂ)) / 2 := by rw [hmu, hc]; ring
      rw [hA, hB, norm_div_two, norm_div_two, hnadd, hnsub]
      norm_num

end Work.TMC7Core.Solutions
