import Mathlib
import Submission.Work.A7.BfunAux
import Submission.Commons.NumberTheory.Linnik.exp_neg_bounds

namespace Work.A7

open Work.LinnikContract

/-!
# Area 7 — `B(K, λ) ≤ B(K, 0)` for `λ > 0`

For `λ ≠ 0` HB's per-character constant is (`BfunAux.Bfun_eq_gAux`)

  `B(K,λ) = 1/(3K) + (2 - 2λ/3) · g(2Kλ)`,   `g(t) = (t - 1 + e^{-t})/t²`,

while `B(K,0) = 1/(3K) + 1`.  For `t = 2Kλ ≥ 0` one has `0 ≤ g(t) ≤ 1/2`
(equivalently `0 ≤ t - 1 + e^{-t} ≤ t²/2`, the linear/second-order Taylor bounds for
`e^{-t}`).  Hence `(2 - 2λ/3)·g(t) ≤ 1` — the product is `≤ 0` when `2 - 2λ/3 ≤ 0`, and
`≤ (2 - 2λ/3)/2 = 1 - λ/3 ≤ 1` otherwise — which is exactly the claim.
-/

/-- `g(t) = (t - 1 + e^{-t})/t² ≥ 0`, since `1 - t ≤ e^{-t}`. -/
private lemma gAux_nonneg (t : ℝ) : 0 ≤ gAux t := by
  rw [gAux]
  refine div_nonneg ?_ (sq_nonneg t)
  have h := Real.one_sub_le_exp_neg t
  linarith

/-- `g(t) ≤ 1/2` for `t ≥ 0`: this is `t - 1 + e^{-t} ≤ t²/2`, i.e. the second order
Taylor lower bound `1 - e^{-t} ≥ t - t²/2`. -/
private lemma gAux_le_half {t : ℝ} (ht : 0 ≤ t) : gAux t ≤ 1 / 2 := by
  rw [gAux]
  have hnum : t - 1 + Real.exp (-t) ≤ t ^ 2 / 2 := by
    have h := (Commons.NumberTheory.Linnik.exp_neg_bounds t ht).2.2
    linarith
  rcases eq_or_lt_of_le ht with h0 | h0
  · subst h0
    norm_num
  · rw [div_le_iff₀ (pow_pos h0 2)]
    nlinarith [hnum]

theorem Bfun_le_at_zero_of_pos {K y : ℝ} (hK : 0 < K) (hy : 0 < y) :
    Work.LinnikContract.Bfun K y ≤ Work.LinnikContract.Bfun K 0 := by
  have hKne : K ≠ 0 := ne_of_gt hK
  have hyne : y ≠ 0 := ne_of_gt hy
  have hbz : Work.LinnikContract.Bfun K 0 = 1 / (3 * K) + 1 := by
    rw [Work.LinnikContract.Bfun, if_pos rfl]
  rw [hbz, Bfun_eq_gAux hKne hyne]
  have ht : 0 ≤ 2 * K * y := by positivity
  have hg0 : 0 ≤ gAux (2 * K * y) := gAux_nonneg (2 * K * y)
  have hgh : gAux (2 * K * y) ≤ 1 / 2 := gAux_le_half ht
  have hprod : (2 - 2 * y / 3) * gAux (2 * K * y) ≤ 1 := by
    by_cases hc : 0 ≤ 2 - 2 * y / 3
    · have h := mul_le_mul_of_nonneg_left hgh hc
      have h2 : (2 - 2 * y / 3) * (1 / 2) = 1 - y / 3 := by ring
      nlinarith [h, hy]
    · have hc' : 2 - 2 * y / 3 ≤ 0 := le_of_lt (not_le.mp hc)
      have h := mul_nonpos_of_nonpos_of_nonneg hc' hg0
      linarith
  linarith

end Work.A7
