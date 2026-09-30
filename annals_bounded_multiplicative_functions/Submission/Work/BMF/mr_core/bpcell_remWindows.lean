import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_direct_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Window bounds for the coarse (`k = 0`) cells

For `j` in the coarse index set `indexSet K (Pc Y) (Qc B Y)` — i.e. for the dyadic-in-log cell
`[e^{j/K}, e^{(j+1)/K}]` meeting `[Pc Y, Qc B Y]` — the associated Buchstab window is

  `W_j = Y * exp (-(j:ℝ)/K)`,

the left end of the cell `[Y e^{-(j+1)/K}, 3 Y e^{-j/K}]` (up to the factor `3`).

This file establishes the crude numerical facts about `W_j` that the remainder/distance
estimates of the `k = 0` core consume:

* `Y e^{-(j+1)/K}` is within a factor `4` of `Y e^{-j/K}` (so the ranges `[X,Y e^{-j/K}]` of the
  Buchstab decomposition have comparable length), for `K ≥ 4`;
* `W_j ≥ 16`, i.e. the windows stay long (`bpc_remWindows` of the paper's §6 bookkeeping);
* the main quantitative input `W_j ≥ 16^4 · Y^{1/2}` — equivalently
  `W_j^{1/4}/16 ≥ Y^{1/8}` — which places the window above the `Y^{1/8}` length threshold where
  the short-interval mean value theorem starts to apply.

The bound `W_j ≥ 16^4 Y^{1/2}` comes from `j ≤ K log Q_c`, i.e. `e^{j/K} ≤ Q_c`, together with the
hypothesis `Q_c = exp (logQc B Y) ≤ Y^{1/2}/16^4` (so `Q_c` is `≤ Y^{1/2 - o(1)}`).
-/

set_option autoImplicit false

namespace Work.BMF.mr_core

/-- Membership in the index set bounds `exp (j/K)` by `Q` (for `j` in the *upper* part of the
range and `Q > 0`): if `j ∈ indexSet K P Q` with `0 < K` and `0 ≤ log Q`, then
`Q⁻¹ ≤ exp (-(j:ℝ)/K)`.

This is the elementary `j ≤ K log Q` content of the index set, and is used whenever a coarse cell
window has to be compared with `Y / Q_c`. -/
lemma indexSet_inv_le_exp {K P Q : ℝ} {j : ℕ} (hK : 0 < K) (hQpos : 0 < Q)
    (hlogQ : 0 ≤ Real.log Q) (hj : j ∈ mrDirect.indexSet K P Q) :
    Q⁻¹ ≤ Real.exp (-(j : ℝ) / K) := by
  have hjle : j ≤ ⌊K * Real.log Q⌋₊ :=
    (Finset.mem_Icc.mp (by rw [mrDirect.indexSet] at hj; exact hj)).2
  have hfl : ((⌊K * Real.log Q⌋₊ : ℕ) : ℝ) ≤ K * Real.log Q := by
    apply Nat.floor_le
    nlinarith
  have hjK : (j : ℝ) ≤ K * Real.log Q := by
    have : (j : ℝ) ≤ ((⌊K * Real.log Q⌋₊ : ℕ) : ℝ) := by exact_mod_cast hjle
    linarith
  have hdiv : (j : ℝ) / K ≤ Real.log Q := by
    rw [div_le_iff₀ hK]
    calc (j : ℝ) ≤ K * Real.log Q := hjK
      _ = Real.log Q * K := by ring
  have h1 : Real.exp (-(Real.log Q)) ≤ Real.exp (-(j : ℝ) / K) :=
    Real.exp_le_exp.mpr (by simpa [neg_div] using neg_le_neg hdiv)
  have h2 : Real.exp (-(Real.log Q)) = Q⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hQpos]
  rwa [h2] at h1

/-- The coarse cell window is at least `16^4·Y^{1/2}`: for `K ≥ 4`, `16^8 ≤ Y`, `j` in the coarse
index set and `exp (logQc B Y) ≤ Y^{1/2}/16^4`,

  `16^4 * Y^{1/2} ≤ Y * exp (-(j:ℝ)/K)`.

In particular (dividing by `16^4` and taking fourth roots) the window satisfies
`(Y exp (-(j:ℝ)/K))^{1/4}/16 ≥ Y^{1/8}`. -/
lemma bpcell_window_lower {B K Y : ℝ} {j : ℕ} (hK : 4 ≤ K) (hY : (16 : ℝ) ^ 8 ≤ Y)
    (hlog : Real.exp (Work.BMF.mrCore.logQc B Y) ≤ Y ^ (1 / 2 : ℝ) / 16 ^ 4)
    (hj : j ∈ mrDirect.indexSet K (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)) :
    (16 : ℝ) ^ 4 * Y ^ (1 / 2 : ℝ) ≤ Y * Real.exp (-(j : ℝ) / K) := by
  have hKpos : 0 < K := by linarith
  have hYpos : 0 < Y := by norm_num at hY ⊢; linarith
  have hY1 : (1 : ℝ) ≤ Y := by norm_num at hY ⊢; linarith
  have hlogPc : 0 ≤ Work.BMF.mrCore.logPc Y := by
    unfold Work.BMF.mrCore.logPc
    exact Real.rpow_nonneg (Real.log_nonneg hY1) _
  have hlogQc : 0 ≤ Real.log (Work.BMF.mrCore.Qc B Y) := by
    rw [show Real.log (Work.BMF.mrCore.Qc B Y) = Work.BMF.mrCore.logQc B Y by
      simp [Work.BMF.mrCore.Qc]]
    exact mul_nonneg (Real.exp_nonneg _) hlogPc
  have hexp_ge : (Work.BMF.mrCore.Qc B Y)⁻¹ ≤ Real.exp (-(j : ℝ) / K) :=
    indexSet_inv_le_exp hKpos (Real.exp_pos _) hlogQc hj
  have hQpos : 0 < Work.BMF.mrCore.Qc B Y := Real.exp_pos _
  have hQle : Work.BMF.mrCore.Qc B Y ≤ Y ^ (1 / 2 : ℝ) / 16 ^ 4 := by
    simpa [Work.BMF.mrCore.Qc] using hlog
  have hinv : (Y ^ (1 / 2 : ℝ) / 16 ^ 4)⁻¹ ≤ (Work.BMF.mrCore.Qc B Y)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) hQpos]
    exact hQle
  have hYh : Y * (Y ^ (1 / 2 : ℝ))⁻¹ = Y ^ (1 / 2 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one Y]
    rw [← Real.rpow_neg (le_of_lt hYpos), ← Real.rpow_add hYpos]
    norm_num
  have h16inv : (Y ^ (1 / 2 : ℝ) / 16 ^ 4)⁻¹ = 16 ^ 4 * (Y ^ (1 / 2 : ℝ))⁻¹ := by
    rw [inv_div, div_eq_mul_inv]
  have hkey : 16 ^ 4 * Y ^ (1 / 2 : ℝ) = Y * (Y ^ (1 / 2 : ℝ) / 16 ^ 4)⁻¹ := by
    rw [h16inv]
    conv_lhs => rw [← hYh]
    ring
  calc (16 : ℝ) ^ 4 * Y ^ (1 / 2 : ℝ) = Y * (Y ^ (1 / 2 : ℝ) / 16 ^ 4)⁻¹ := hkey
    _ ≤ Y * (Work.BMF.mrCore.Qc B Y)⁻¹ := mul_le_mul_of_nonneg_left hinv (le_of_lt hYpos)
    _ ≤ Y * Real.exp (-(j : ℝ) / K) := mul_le_mul_of_nonneg_left hexp_ge (le_of_lt hYpos)

theorem bpcell_remWindows {B K Y : ℝ} {j : ℕ} (hK : 4 ≤ K) (hY : (16 : ℝ) ^ 8 ≤ Y)
    (hlog : Real.exp (Work.BMF.mrCore.logQc B Y) ≤ Y ^ (1 / 2 : ℝ) / 16 ^ 4)
    (hj : j ∈ Work.BMF.mrDirect.indexSet K (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)) :
    (16 : ℝ) ≤ Y * Real.exp (-(j : ℝ) / K) ∧
    Y ^ (1 / 8 : ℝ) ≤ (Y * Real.exp (-(j : ℝ) / K)) ^ (1 / 4 : ℝ) / 16 ∧
    (Y * Real.exp (-(j : ℝ) / K)) / 4 ≤ Y * Real.exp (-((j : ℝ) + 1) / K) ∧
    Y * Real.exp (-((j : ℝ) + 1) / K) ≤ 3 * Y * Real.exp (-(j : ℝ) / K) ∧
    3 * Y * Real.exp (-(j : ℝ) / K) ≤ 4 * (Y * Real.exp (-(j : ℝ) / K)) := by
  have hYpos : 0 < Y := by norm_num at hY ⊢; linarith
  have hW : (16 : ℝ) ^ 4 * Y ^ (1 / 2 : ℝ) ≤ Y * Real.exp (-(j : ℝ) / K) :=
    bpcell_window_lower hK hY hlog hj
  have hYhalf : (16 : ℝ) ^ 4 ≤ Y ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow Y, Real.le_sqrt (by positivity) (by positivity)]
    norm_num at hY ⊢
    linarith
  have hWbig : (16 : ℝ) ^ 8 ≤ Y * Real.exp (-(j : ℝ) / K) := by
    calc (16 : ℝ) ^ 8 = (16 : ℝ) ^ 4 * (16 : ℝ) ^ 4 := by norm_num
      _ ≤ (16 : ℝ) ^ 4 * Y ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hYhalf (by norm_num)
      _ ≤ Y * Real.exp (-(j : ℝ) / K) := hW
  have hYquart : (Y ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) = Y ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hYpos)]
    norm_num
  have h16quart : ((16 : ℝ) ^ 4) ^ (1 / 4 : ℝ) = 16 := by
    rw [← Real.rpow_natCast (16 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
    rw [show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one]
  have hquart : ((16 : ℝ) ^ 4 * Y ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) = 16 * Y ^ (1 / 8 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity), hYquart, h16quart]
  have hexp1 : Real.exp (-((j : ℝ) + 1) / K) =
      Real.exp (-(j : ℝ) / K) * Real.exp (-(1 / K)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hquartlt : (1 / 4 : ℝ) ≤ Real.exp (-(1 / K)) := by
    have ha : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-(1 / K)) := by
      apply Real.exp_le_exp.mpr
      have hle : 1 / K ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hK
      linarith
    have hb : (1 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by
      have := Real.add_one_le_exp (-(1 / 4 : ℝ))
      linarith
    linarith
  have hexp_le1 : Real.exp (-((j : ℝ) + 1) / K) ≤ Real.exp (-(j : ℝ) / K) := by
    rw [hexp1]
    have h : Real.exp (-(1 / K)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (by positivity))
    calc Real.exp (-(j : ℝ) / K) * Real.exp (-(1 / K)) ≤ Real.exp (-(j : ℝ) / K) * 1 :=
          mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
      _ = Real.exp (-(j : ℝ) / K) := by ring
  have hw : (0 : ℝ) ≤ Y * Real.exp (-(j : ℝ) / K) :=
    mul_nonneg (le_of_lt hYpos) (Real.exp_nonneg _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc (16 : ℝ) ≤ (16 : ℝ) ^ 8 := by norm_num
      _ ≤ Y * Real.exp (-(j : ℝ) / K) := hWbig
  · have h4 : (16 * Y ^ (1 / 8 : ℝ)) ≤ (Y * Real.exp (-(j : ℝ) / K)) ^ (1 / 4 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ 4 * Y ^ (1 / 2 : ℝ)) hW
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [hquart] at this
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    linarith
  · calc (Y * Real.exp (-(j : ℝ) / K)) / 4 = (Y * Real.exp (-(j : ℝ) / K)) * (1 / 4) := by ring
      _ ≤ (Y * Real.exp (-(j : ℝ) / K)) * Real.exp (-(1 / K)) :=
          mul_le_mul_of_nonneg_left hquartlt hw
      _ = Y * (Real.exp (-(j : ℝ) / K) * Real.exp (-(1 / K))) := by ring
      _ = Y * Real.exp (-((j : ℝ) + 1) / K) := by rw [← hexp1]
  · calc Y * Real.exp (-((j : ℝ) + 1) / K) ≤ Y * Real.exp (-(j : ℝ) / K) :=
          mul_le_mul_of_nonneg_left hexp_le1 (le_of_lt hYpos)
      _ ≤ 3 * (Y * Real.exp (-(j : ℝ) / K)) := by
          have := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) hw
          simpa using this
      _ = 3 * Y * Real.exp (-(j : ℝ) / K) := by ring
  · calc 3 * Y * Real.exp (-(j : ℝ) / K) = 3 * (Y * Real.exp (-(j : ℝ) / K)) := by ring
      _ ≤ 4 * (Y * Real.exp (-(j : ℝ) / K)) := by linarith

end Work.BMF.mr_core
