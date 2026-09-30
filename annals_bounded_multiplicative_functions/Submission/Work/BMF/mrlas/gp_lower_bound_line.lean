import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.mrlas.Psi2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

theorem gp_lower_bound_line (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {c : ℝ} (hc : 1 < c) (p : ℕ) (hp : p.Prime) {z : ℂ} (hz : c ≤ z.re) :
    1 - 2 * (2 : ℝ) ^ (-c) ≤ ‖Work.BMF.gp f p z‖ := by
  have hz0 : 0 < z.re := lt_of_lt_of_le (by linarith) hz
  -- Write `gp - 1` as the tail `Σ_e f(p^{e+1}) (p^{e+1})^{-z}` and bound it.
  have hgp1 : ‖Work.BMF.gp f p z - 1‖ ≤ 2 * (2 : ℝ) ^ (-c) := by
    have h1 : Work.BMF.gp f p z - 1 = ∑' e : ℕ, LSeries.term f z (p ^ (e + 1)) := by
      rw [Work.BMF.gp_eq_one_add_tail f hf1 hb hp hz0, add_sub_cancel_left]
    rw [h1]
    refine le_trans (Work.BMF.gp_tail_bound f hf1 hb hp hz hc) ?_
    exact mul_le_mul_of_nonneg_left
      (Work.BMF.rpow_neg_anti (x := (2 : ℝ)) (y := (p : ℝ)) (σ := c)
        (by norm_num) (by exact_mod_cast hp.two_le) (by linarith : (0:ℝ) ≤ c)) (by norm_num)
  have h2 : ‖(1 : ℂ) - Work.BMF.gp f p z‖ ≤ 2 * (2 : ℝ) ^ (-c) := by
    rw [norm_sub_rev (1 : ℂ) (Work.BMF.gp f p z)]
    exact hgp1
  have h := norm_sub_norm_le (1 : ℂ) (Work.BMF.gp f p z)
  rw [norm_one] at h
  linarith [h, h2]

end Work.BMF.mrlas
