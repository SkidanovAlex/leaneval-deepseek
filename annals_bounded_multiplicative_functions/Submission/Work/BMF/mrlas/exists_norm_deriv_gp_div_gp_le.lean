import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.Kser_gp_bounds
import Submission.Work.BMF.mrlas.Psi2_defs
import Submission.Work.BMF.mrlas.Psi2_dev
import Submission.Work.BMF.mrlas.norm_tsum_e_mul_u_pow_le
import Submission.Work.BMF.mrlas.gp_lower_bound_line

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Finset Real Complex MeasureTheory
open scoped BigOperators

/-- Uniform-in-`p` bound for the logarithmic derivative of the local Euler factor
`g_p(s) = Σ_e f(p^e) p^{-es}`: for `Re s > 1` it is `O(log p · p^{-Re s})`. -/
theorem exists_norm_deriv_gp_div_gp_le (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      ‖deriv (Work.BMF.gp f p) s / Work.BMF.gp f p s‖
        ≤ C * (Real.log p * (p : ℝ) ^ (-s.re)) := by
  set A : ℝ := ∑' e : ℕ, (e : ℝ) * (1 / 2 : ℝ) ^ (e - 1) with hA
  set c₀ : ℝ := 1 - 2 * (2 : ℝ) ^ (-s.re) with hc0
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact tsum_nonneg (fun e => mul_nonneg (Nat.cast_nonneg e) (pow_nonneg (by norm_num) _))
  have hc0pos : 0 < c₀ := by
    rw [hc0]
    have := Work.BMF.two_mul_rpow_neg_two_lt_one hs
    linarith
  refine ⟨(A + 1) / c₀, div_pos (by linarith) hc0pos, ?_⟩
  intro p hp
  have hlb : c₀ ≤ ‖Work.BMF.gp f p s‖ := by
    rw [hc0]
    exact gp_lower_bound_line f hf1 hb hs p hp le_rfl
  have hgp_pos : 0 < ‖Work.BMF.gp f p s‖ := lt_of_lt_of_le hc0pos hlb
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hpow : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  have hT := norm_tsum_e_mul_u_pow_le f hb hp hs
  have hT' : ‖∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e‖
      ≤ (A + 1) * (p : ℝ) ^ (-s.re) := by
    rw [hA]
    calc ‖∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e‖
        ≤ (∑' e : ℕ, (e : ℝ) * (1 / 2 : ℝ) ^ (e - 1)) * (p : ℝ) ^ (-s.re) := hT
      _ ≤ (∑' e : ℕ, (e : ℝ) * (1 / 2 : ℝ) ^ (e - 1)) * (p : ℝ) ^ (-s.re)
            + (p : ℝ) ^ (-s.re) := le_add_of_nonneg_right hpow
      _ = ((∑' e : ℕ, (e : ℝ) * (1 / 2 : ℝ) ^ (e - 1)) + 1) * (p : ℝ) ^ (-s.re) := by ring
  have hnum : ‖deriv (Work.BMF.gp f p) s‖ ≤ Real.log p * (A + 1) * (p : ℝ) ^ (-s.re) := by
    rw [deriv_gp f hb hp hs, norm_mul, norm_neg]
    have hlogC : ‖(Real.log p : ℂ)‖ = Real.log p := by
      rw [Complex.norm_real, Real.norm_of_nonneg hlog]
    calc ‖(Real.log p : ℂ)‖ * ‖∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e‖
        = Real.log p * ‖∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e‖ := by rw [hlogC]
      _ ≤ Real.log p * ((A + 1) * (p : ℝ) ^ (-s.re)) := mul_le_mul_of_nonneg_left hT' hlog
      _ = Real.log p * (A + 1) * (p : ℝ) ^ (-s.re) := by ring
  rw [norm_div]
  calc ‖deriv (Work.BMF.gp f p) s‖ / ‖Work.BMF.gp f p s‖
      ≤ (Real.log p * (A + 1) * (p : ℝ) ^ (-s.re)) / c₀ := by
        rw [div_le_div_iff₀ hgp_pos hc0pos]
        exact mul_le_mul hnum hlb hc0pos.le (le_trans (norm_nonneg _) hnum)
    _ = (A + 1) / c₀ * (Real.log p * (p : ℝ) ^ (-s.re)) := by ring

end Work.BMF.mrlas
