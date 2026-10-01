import Mathlib
import Submission.Work.A7.BfunAux

namespace Work.A7

/-- For `t < 0`, `gAux t = (t - 1 + e^{-t})/t² ≥ 1/2`.  Writing `u = -t > 0`, this is the
truncated Taylor bound `1 + u + u²/2 ≤ e^u`. -/
private lemma gAux_ge_half_of_neg {t : ℝ} (ht : t < 0) : (1 / 2 : ℝ) ≤ gAux t := by
  unfold gAux
  have hu : 0 ≤ -t := by linarith
  have hsum : 1 + (-t) + (-t) ^ 2 / 2 ≤ Real.exp (-t) :=
    Real.quadratic_le_exp_of_nonneg hu
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero (ne_of_lt ht)
  rw [le_div_iff₀ ht2]
  nlinarith [hsum]

/-- At `λ = 0` the value `Bfun K 0 = 1/(3K) + 1` is a lower bound for `Bfun K x` for every
`x < 0`.  Using `Bfun_eq_gAux`, `Bfun K x = 1/(3K) + (2 - 2x/3)·gAux(2Kx)`; here the factor
`2 - 2x/3 ≥ 2` while `gAux(2Kx) ≥ 1/2` because `2Kx < 0`, so the product is at least `1`. -/
theorem le_Bfun_at_zero_of_neg {K x : ℝ} (hK : 0 < K) (hx : x < 0) :
    Work.LinnikContract.Bfun K 0 ≤ Work.LinnikContract.Bfun K x := by
  have hKne : K ≠ 0 := ne_of_gt hK
  have hxne : x ≠ 0 := ne_of_lt hx
  have hB0 : Work.LinnikContract.Bfun K 0 = 1 / (3 * K) + 1 := by
    rw [Work.LinnikContract.Bfun, if_pos rfl]
  have hBx : Work.LinnikContract.Bfun K x
      = 1 / (3 * K) + (2 - 2 * x / 3) * gAux (2 * K * x) :=
    Bfun_eq_gAux hKne hxne
  rw [hB0, hBx]
  have hs : 2 * K * x < 0 := by nlinarith [hK, hx]
  have hg : (1 / 2 : ℝ) ≤ gAux (2 * K * x) := gAux_ge_half_of_neg hs
  have hcoef : (2 : ℝ) ≤ 2 - 2 * x / 3 := by nlinarith [hx]
  have hprod : (2 : ℝ) * (1 / 2) ≤ (2 - 2 * x / 3) * gAux (2 * K * x) :=
    mul_le_mul hcoef hg (by norm_num) (by linarith)
  linarith

end Work.A7
