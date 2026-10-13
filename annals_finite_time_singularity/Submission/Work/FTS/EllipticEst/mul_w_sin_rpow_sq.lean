import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- Algebraic identity underlying the weight computation: for a nonnegative base `s` and any
real exponent `e`, the square of `a * (w / s ^ e)` collects the powers of `s` into a single
real power, `(a * (w / s ^ e))² = a² w² s^{-2e}`.  (`s = 0` is allowed: both sides vanish
thanks to Lean's totalised `x ^ e = 0` for `x = 0`, `e ≠ 0`.) -/
private lemma mul_div_rpow_sq (a w s e : ℝ) (hs : 0 ≤ s) :
    (a * (w / s ^ e)) ^ 2 = a ^ 2 * w ^ 2 * s ^ (-(2 * e)) := by
  have h2 : (s ^ e) ^ ((2 : ℕ) : ℝ) = s ^ (e * ((2 : ℕ) : ℝ)) :=
    (Real.rpow_mul hs e ((2 : ℕ) : ℝ)).symm
  have he : e * ((2 : ℕ) : ℝ) = 2 * e := by ring
  rw [mul_pow, div_pow, ← Real.rpow_natCast (s ^ e) 2, h2, he]
  rw [div_eq_mul_inv, ← Real.rpow_neg hs (2 * e)]
  ring

theorem mul_w_sin_rpow_sq (a w : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (a * (w / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = a ^ 2 * w ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have he : 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta := by
    norm_num [Work.Spaces.eta]
  have h := mul_div_rpow_sq a w (Real.sin (2 * θ)) (Work.Spaces.eta / 2) hs
  rw [he] at h
  exact h

end Work.FTS.EllipticEst
