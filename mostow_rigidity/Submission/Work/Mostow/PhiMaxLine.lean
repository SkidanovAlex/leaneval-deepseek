import Mathlib

/-!
# The two-point perturbation used in the study of `max matF`

For `x : Fin n → ℝ` and two indices `i ≠ j`, `TwoPtLine x i j t` is the point obtained from `x`
by moving mass `t` from coordinate `j` to coordinate `i` (the coordinate `i` becomes `x i + t`,
the coordinate `j` becomes `x j - t`, and all other coordinates stay put).  This is the
perturbation that turns the Lagrange condition for the maximum of
`matF lam = (∏ √lamᵢ)/(∏ (1 - lamᵢ))` on the box `Kset n δ` into
`matPhi (x i) = matPhi (x j)`.

This file only contains the definition and the elementary bookkeeping lemmas about it.
-/

namespace Work.Mostow

noncomputable section

open scoped BigOperators

/-- The two-point perturbation of `x`: move mass `t` from coordinate `j` to coordinate `i`. -/
def TwoPtLine {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) (t : ℝ) : Fin n → ℝ :=
  fun k => x k + t * ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0))

/-- The sum of the perturbation direction is zero. -/
lemma twoPtLine_dir_sum {n : ℕ} (i j : Fin n) :
    (∑ k : Fin n, ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0))) = 0 := by
  rw [Finset.sum_sub_distrib]
  simp

@[simp] lemma TwoPtLine_zero {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
    TwoPtLine x i j 0 = x := by
  funext k; simp [TwoPtLine]

lemma TwoPtLine_apply_left {n : ℕ} (x : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    TwoPtLine x i j t i = x i + t := by
  simp [TwoPtLine, hij]

lemma TwoPtLine_apply_right {n : ℕ} (x : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    TwoPtLine x i j t j = x j - t := by
  simp [TwoPtLine, hij.symm, sub_eq_add_neg]

lemma TwoPtLine_apply_of_ne {n : ℕ} (x : Fin n → ℝ) {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j)
    (t : ℝ) : TwoPtLine x i j t k = x k := by
  simp [TwoPtLine, hki, hkj]

/-- The perturbation preserves the sum of the coordinates. -/
lemma twoPtLine_sum {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    ∑ k, TwoPtLine x i j t k = ∑ k, x k := by
  have h1 : (∑ k, TwoPtLine x i j t k)
      = ∑ k, x k + t * ∑ k, ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0)) := by
    simp only [TwoPtLine, Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1, twoPtLine_dir_sum, mul_zero, add_zero]

/-- The derivative of the coordinates of the perturbation line. -/
lemma hasDerivAt_TwoPtLine {n : ℕ} (x : Fin n → ℝ) (i j k : Fin n) :
    HasDerivAt (fun t : ℝ => TwoPtLine x i j t k)
      ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0)) 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).mul_const
    ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0))
  simp only [TwoPtLine]
  simpa using h.const_add (x k)

end

end Work.Mostow
