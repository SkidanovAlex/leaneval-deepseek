import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Linarith.Frontend

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The odd extension of a real function

This file defines the odd extension (about `0`) of a real function `F : ℝ → ℝ`, as a
complex-valued function, together with its elementary properties.  It is the auxiliary
notion used in `Work.FTS.EllipticEst.sin_complete_Ioc`: a function in `L²(0,L)` all of
whose sine coefficients `∫_0^L F θ sin (n π θ / L) dθ` vanish must vanish a.e., because
its odd extension to `(-L,L)` has all Fourier coefficients zero.
-/

namespace Work.FTS.EllipticEst

/-- The odd extension (about `0`) of a real function `F`, as a complex-valued function:
`F x` for `x > 0`, `-F (-x)` for `x < 0`, and `0` at `0`. -/
noncomputable def sinOdd (F : ℝ → ℝ) : ℝ → ℂ :=
  fun x => if 0 < x then (F x : ℂ) else if x < 0 then -(F (-x) : ℂ) else 0

lemma sinOdd_of_pos {F : ℝ → ℝ} {x : ℝ} (h : 0 < x) : sinOdd F x = (F x : ℂ) := by
  simp [sinOdd, h]

lemma sinOdd_of_neg {F : ℝ → ℝ} {x : ℝ} (h : x < 0) : sinOdd F x = -(F (-x) : ℂ) := by
  simp [sinOdd, h, not_lt.mpr h.le]

lemma sinOdd_zero (F : ℝ → ℝ) : sinOdd F 0 = 0 := by
  simp [sinOdd]

/-- The defining oddness of `sinOdd`, valid also at `0`. -/
lemma sinOdd_neg (F : ℝ → ℝ) (x : ℝ) : sinOdd F (-x) = -sinOdd F x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sinOdd_of_pos (by linarith : 0 < -x), sinOdd_of_neg h, neg_neg]
  · rw [h]; simp [sinOdd]
  · rw [sinOdd_of_neg (by linarith : -x < 0), sinOdd_of_pos h, neg_neg]

end Work.FTS.EllipticEst
