import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.PsiWt

theorem Dth_sq_sin_rpow_le_HkIntegrand {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a))
      ≤ Work.Spaces.HkIntegrand a 4 f z θ := by
  -- `D_θ f = D_z^0 D_θ^1 f` is the mixed slot `(i,j) = (1,0)` of the `H^4` integrand, so it
  -- suffices to compare the two expressions.  Both the extra factor `w z ≥ 1` (for `z > 0`)
  -- and the identity `sin(2θ)^{-γ} = (sin(2θ)^{-γ/2})²` (for `sin(2θ) > 0`, i.e. on the open
  -- angular interval) only make that slot larger than the left-hand side.
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by have := Real.pi_pos; linarith [hθ.2])
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a)) :=
    Real.rpow_nonneg (le_of_lt hs) _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hz]
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ hw1
  have hsq : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam a / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a)) := by
    rw [sq, ← Real.rpow_add hs,
      show -(Work.Spaces.gam a / 2) + -(Work.Spaces.gam a / 2) = -(Work.Spaces.gam a) by ring]
  have hterm : (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt a z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand a 4 f z θ :=
    Work.Spaces.sq_le_HkIntegrand_mixed a 4 f z θ 1 0 le_rfl (by norm_num)
  refine le_trans ?_ hterm
  have hmix : Work.Spaces.mixed 0 1 f = Work.Spaces.Dth f := rfl
  rw [hmix]
  calc (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a))
      = (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a)) * 1 := by
        ring
    _ ≤ (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a))
          * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_left hw2 (mul_nonneg (sq_nonneg _) hsnn)
    _ = (Work.Spaces.Dth f z θ
          * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam a / 2)))) ^ 2 := by
        rw [mul_pow, mul_pow, hsq]; ring
    _ = (Work.Spaces.Dth f z θ * Work.Spaces.Wt a z θ) ^ 2 := by
        rw [Work.Spaces.Wt, Work.Spaces.wTheta]

end Work.FTS.FireFix.Clauses.PsiWt
