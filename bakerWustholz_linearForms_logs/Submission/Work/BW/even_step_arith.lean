import Mathlib
import Submission.Work.BW.even_step_defs
import Submission.Work.BW.num_T
import Submission.Work.BW.num_xi
import Submission.Work.BW.evenU_le
import Submission.Work.BW.evenW_ge
import Submission.Work.BW.evenV_le
import Submission.Work.BW.evenY_le
import Submission.Work.BW.evenXlog_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The two numerical conditions of the even step (BW pp. 57–58), for all `r ≥ 2`, `d ≥ 1`, `h ≥ 19`, `σ_j ≥ 1/d` and all levels `J` with `J+1 ≤ I = ⌊50 log(2rd)⌋` in the non-degenerate regime `∃j, 2^J ≤ D_j`:

* (𝒥-part) `log(R/δ) + U - W < -log 2`: `R = 7.2S'`, `δ = 5S'`, `U` the `(16)`-exponent at level `J+1` and `W = (T'+1)X log(R/(X+2))` the `(23')`-bound for the lacunary product `B'(·;X)`, `X = 2S'`;
* (ℐ-part) `log(X(T'+1)) + log(η/(κ-η)) + V + Y < -log 2`: `V` the `(21)`-exponent at level `J+1` and `Y = (T'+1)(X + 2log X + 3)` the `(25)`-bound for `B'`.

The non-degeneracy hypothesis enters only through `q = ξ^{-rJ}/D ≤ (2ξ^r)^{-J}/r ≤ 1/r ≤ 1/2`, which absorbs the `+1` in `T'+1` (the term `ξ^{-rJ}S/(SD)` of `X/(SD)`); without it the ℐ-part fails for large `J`. Checked numerically (over `r ≤ 30`, `d ≤ 10`, `h ≤ 10^3`, `σ_j ≥ 1/d`, all admissible `J`): worst margins `-6.38 SD` and `-16.8 SD`. -/
theorem even_step_arith {r d h : ℕ} {σ : Fin r → ℝ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (J : ℕ) (hJ : J + 1 ≤ pI r d)
    (hnd : ∃ j, (2 : ℝ) ^ J ≤ (pDj r d σ j : ℝ)) :
    Real.log (evR r J (pS r d h : ℝ) / evdelta r J (pS r d h : ℝ)) + evU r d h σ J - evW r d h σ J
        < -Real.log 2 ∧
      Real.log ((evX r J (pS r d h : ℝ) : ℝ) * (((evTp r J (pT r d σ : ℝ)) + 1 : ℕ) : ℝ))
        + Real.log ((1 / 3) / (1 - 1 / 3)) + evV r d h σ J + evY r d h σ J < -Real.log 2 := by
  have hUle := evenU_le hr hd hh hσ J hJ
  have hWge := evenW_ge hr hd hh hσ J hJ
  have hVle := evenV_le hr hd hh hσ J hJ
  have hYle := evenY_le hr hd hh hσ J hJ hnd
  have hXlog := evenXlog_le hr hd hh hσ J hJ hnd
  have hS608 : (608:ℝ) ≤ (pS r d h : ℝ) := (num_T hr hd hh σ hσ).2.2.2
  have hD1 : (1:ℝ) ≤ pD r d σ := pD_ge_one hr hd σ hσ
  have hS0 : (0:ℝ) ≤ (pS r d h : ℝ) := by linarith
  have hD0 : (0:ℝ) < pD r d σ := by linarith
  have hSDpos : (0:ℝ) < (pS r d h : ℝ) * pD r d σ := mul_pos (by linarith) hD0
  have hSD608 : (608:ℝ) ≤ (pS r d h : ℝ) * pD r d σ := by
    calc (608:ℝ) = 608 * 1 := by ring
      _ ≤ (pS r d h : ℝ) * pD r d σ := mul_le_mul hS608 hD1 (by norm_num) hS0
  have hpx : (0:ℝ) < pxi r := pxi_pos hr
  have hxi_inv : (1:ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_eq_one_div]
    have h1 : pxi r ^ (r*J) ≤ 1 := pow_le_one₀ hpx.le (pxi_le_one r)
    have h0 : 0 < pxi r ^ (r*J) := pow_pos hpx (r*J)
    exact (one_le_div h0).mpr h1
  have hxi_inv0 : (0:ℝ) ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) := le_trans (by norm_num) hxi_inv
  have hSP1216 : (1216:ℝ) ≤ (evSP r J (pS r d h : ℝ) : ℝ) := by
    have hfloor : (1216:ℕ) ≤ evSP r J (pS r d h : ℝ) := by
      apply Nat.le_floor
      have h4 : (1:ℝ) * 608 ≤ pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ) :=
        mul_le_mul hxi_inv hS608 (by norm_num) hxi_inv0
      norm_num at h4 ⊢
      nlinarith [h4]
    exact_mod_cast hfloor
  have hSPpos : (0:ℝ) < (evSP r J (pS r d h : ℝ) : ℝ) := by linarith
  have hlog1 : Real.log (evR r J (pS r d h : ℝ) / evdelta r J (pS r d h : ℝ)) ≤ 1 := by
    have hne : (evSP r J (pS r d h : ℝ) : ℝ) ≠ 0 := ne_of_gt hSPpos
    have hratio : evR r J (pS r d h : ℝ) / evdelta r J (pS r d h : ℝ) = 7.2 / 5 := by
      simp only [evR, evdelta]
      exact mul_div_mul_right (7.2) 5 hne
    rw [hratio]
    refine (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 7.2/5)).mpr ?_
    have hexp : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have : (7.2/5:ℝ) ≤ 2 := by norm_num
    linarith
  constructor
  · have hSDbig : (1.7:ℝ) < (13.4 - 13.27) * ((pS r d h : ℝ) * pD r d σ) := by
      have h1 : (13.4 - 13.27 : ℝ) = 0.13 := by norm_num
      rw [h1]
      have h2 : (0.13:ℝ) * 608 ≤ 0.13 * ((pS r d h : ℝ) * pD r d σ) :=
        mul_le_mul_of_nonneg_left hSD608 (by norm_num)
      linarith
    have hgoal : (13.4 - 13.27) * ((pS r d h : ℝ) * pD r d σ)
        = 13.4 * (pS r d h : ℝ) * pD r d σ - 13.27 * (pS r d h : ℝ) * pD r d σ := by ring
    nlinarith [hUle, hWge, hlog1, hSDbig, hgoal, Real.log_two_lt_d9]
  · have hhalf : Real.log ((1 / 3) / (1 - 1 / 3)) = -Real.log 2 := by
      have h : (1/3 : ℝ) / (1 - 1/3) = (2:ℝ)⁻¹ := by norm_num
      rw [h, Real.log_inv]
    rw [hhalf]
    have hr1 : 1 ≤ r := by omega
    have hxir : pxi r ^ r ≤ 0.732 := by
      have h := (num_xi hr).2.2.1
      calc pxi r ^ r = pxi r ^ ((r-1)+1) := by rw [Nat.sub_add_cancel hr1]
        _ = pxi r ^ (r-1) * pxi r := by rw [pow_succ]
        _ ≤ 0.732 * 1 := mul_le_mul h (pxi_le_one r) hpx.le (by norm_num)
        _ = 0.732 := by ring
    have h2r : (4:ℝ) ≤ (2:ℝ)^r := by
      calc (4:ℝ) = (2:ℝ)^2 := by norm_num
        _ ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num) hr
    have hx25 : 25.2 * pxi r ^ r ≤ 25.2 * 0.732 := mul_le_mul_of_nonneg_left hxir (by norm_num)
    have h29 : 9 * (4:ℝ) ≤ 9 * (2:ℝ)^r := mul_le_mul_of_nonneg_left h2r (by norm_num)
    have hcoef : (8.11 - 9 * (2:ℝ)^r) + (25.2 * pxi r ^ r + 2.2) + 1 < 0 := by nlinarith [hx25, h29]
    have hsum : evV r d h σ J + evY r d h σ J
        + Real.log ((evX r J (pS r d h : ℝ) : ℝ) * (((evTp r J (pT r d σ : ℝ)) + 1 : ℕ) : ℝ))
        ≤ ((8.11 - 9 * (2:ℝ)^r) + (25.2 * pxi r ^ r + 2.2) + 1) * ((pS r d h : ℝ) * pD r d σ) := by
      nlinarith [hVle, hYle, hXlog]
    have hneg : ((8.11 - 9 * (2:ℝ)^r) + (25.2 * pxi r ^ r + 2.2) + 1) * ((pS r d h : ℝ) * pD r d σ) < 0 :=
      mul_neg_of_neg_of_pos hcoef hSDpos
    linarith [hsum, hneg]

end Work.BW
