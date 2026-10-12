import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Word
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.paramsAt_facts`

The elementary facts about FS's parameter block at the concrete choice
`paramsAt μ a = fsParams (μa³)` that every consumer of the block needs:
under the diluteness hypothesis `ParamsOK (paramsAt μ a) (μa³)` (and `μ > 0`),

* the scattering length is positive, `0 < a`;
* the small dimensionless parameters `d = X⁶`, `s = X` and the gap `ε_T = X^{23/4}`
  are positive, `ε_T ≤ 1`, and `b = 1/16 ≥ 0`;
* the localisation constant `K_ℓ = X^{-3/2}` is positive.

All of this is *forced* by `sec:params` itself — no smallness of `μa³` is assumed
beyond what `ParamsOK` encodes:

* `con:sKell` (`1 ≪ sK_ℓ = X^{-1/2}`, whose left-hand side is the constant `1`)
  fails at `t = μa³ = 0`, where every parameter of `fsParams t` vanishes
  (`Real.zero_rpow`): `t = 0` would give `1 ≤ 0`;
* `con:KellKLd` (`d^{2M-2} = X^{564} ≪ (μa³)^{1/2}`, whose right-hand side is
  `t^{1/2}`) fails at `t < 0`: there Lean's `t^(1/2) = exp(log t / 2)·cos(π/2) = 0`
  (`Real.rpow_def_of_nonpos`, `Real.cos_pi_div_two`) while
  `d = t^{6/323} = exp((6/323)log t)·cos(6π/323) > 0`
  (`Real.cos_pos_of_mem_Ioo`, since `6/323 < 1/2`), so `0 < d^{94} ≤ 0`.
  Hence `μa³ = t > 0`, i.e. `a > 0`;
* `con:KellKLd` at `0 < t = μa³` is `t^{564/323} ≤ t^{1/2+ε}` with `ε ≤ 1/40`;
  for `t > 1` this reads `564/323 ≤ 1/2 + ε ≤ 21/40`, which is false
  (`Real.rpow_le_rpow_left_iff`). Hence `t ≤ 1`, and then `ε_T = t^{23/(4·323)} ≤ 1`.

This is the `0 < a`-and-`t ≤ 1` bookkeeping that lets later statements drop
hypotheses on `a` and on the size of `μa³`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox

theorem paramsAt_facts {μ a : ℝ} (hμ : 0 < μ)
    (hP : Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt μ a) (μ * a ^ 3)) :
    0 < a ∧ 0 < (Work.BoseBox.paramsAt μ a).d ∧ 0 < (Work.BoseBox.paramsAt μ a).s
      ∧ 0 ≤ (Work.BoseBox.paramsAt μ a).eT ∧ (Work.BoseBox.paramsAt μ a).eT ≤ 1
      ∧ 0 ≤ (Work.BoseBox.paramsAt μ a).b ∧ 0 < (Work.BoseBox.paramsAt μ a).Kl := by
  -- `con:sKell` (at `t = 0`) and `con:KellKLd` (at `t < 0`) force `t = μa³ > 0`,
  -- hence `a > 0` because `μ > 0`.
  have ha : 0 < a := by
    by_contra ha
    have ha' : a ≤ 0 := not_lt.mp ha
    have h3 : a ^ 3 ≤ 0 := by nlinarith [sq_nonneg a]
    have ht0 : μ * a ^ 3 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ.le h3
    rcases lt_or_eq_of_le ht0 with hlt | heq
    · -- `t < 0`: `con:KellKLd` reads `d^{94} ≤ t^{1/2}·t^ε = 0`, but `d^{94} > 0`.
      have hne : μ * a ^ 3 ≠ 0 := ne_of_lt hlt
      have hd : 0 < (paramsAt μ a).d := by
        have hds : (paramsAt μ a).d = ((μ * a ^ 3) : ℝ) ^ ((6 : ℝ) / 323) := by
          simp [paramsAt, fsParams, fsXp]
        rw [hds, Real.rpow_def_of_nonpos hlt.le, if_neg hne]
        exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo
          ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩)
      obtain ⟨ε, hε0, hεs, hineq⟩ := hP.KellKLd
      have h12 : (μ * a ^ 3) ^ ((1 : ℝ) / 2) = 0 := by
        rw [Real.rpow_def_of_nonpos hlt.le, if_neg hne]
        rw [show (1 : ℝ) / 2 * Real.pi = Real.pi / 2 by ring, Real.cos_pi_div_two, mul_zero]
      rw [h12, zero_mul] at hineq
      have hpos := Real.rpow_pos_of_pos hd (2 * ((paramsAt μ a).M : ℝ) - 2)
      linarith
    · -- `t = 0`: every parameter vanishes, so `con:sKell` reads `1 ≤ 0`.
      obtain ⟨ε, hε0, hεs, hineq⟩ := hP.sKell
      have hs : (paramsAt μ a).s = 0 := by
        have hss : (paramsAt μ a).s = ((μ * a ^ 3) : ℝ) ^ ((1 : ℝ) / 323) := by
          simp [paramsAt, fsParams, fsXp]
        rw [hss, heq]
        exact Real.zero_rpow (by norm_num)
      have hKl : (paramsAt μ a).Kl = 0 := by
        have hKls : (paramsAt μ a).Kl = fsXp (μ * a ^ 3) (-(3 / 2)) := by
          simp [paramsAt, fsParams]
        rw [hKls, heq]
        simp only [fsXp]
        exact Real.zero_rpow (by norm_num)
      have hte : (μ * a ^ 3) ^ ε = 0 := by
        rw [heq]
        exact Real.zero_rpow (ne_of_gt hε0)
      rw [hs, hKl, hte] at hineq
      norm_num at hineq
  have ht : 0 < μ * a ^ 3 := by positivity
  -- `con:KellKLd` at `0 < t` forces `t ≤ 1`: otherwise `t^{564/323} ≤ t^{21/40}`.
  have ht1 : μ * a ^ 3 ≤ 1 := by
    by_contra h
    have h1 : 1 < μ * a ^ 3 := not_le.mp h
    obtain ⟨ε, hε0, hεs, hineq⟩ := hP.KellKLd
    have hLHS : (paramsAt μ a).d ^ (2 * ((paramsAt μ a).M : ℝ) - 2)
        = (μ * a ^ 3) ^ ((564 : ℝ) / 323) := by
      have hds : (paramsAt μ a).d = fsXp (μ * a ^ 3) 6 := by
        simp [paramsAt, fsParams]
      have hMs : ((paramsAt μ a).M : ℝ) = 48 := by
        simp [paramsAt, fsParams, mValue]
      rw [hds, hMs]
      rw [show 2 * (48 : ℝ) - 2 = 94 by norm_num, fsXp_rpow ht.le]
      simp only [fsXp]
      norm_num
    have hcmp : (μ * a ^ 3) ^ ((564 : ℝ) / 323) ≤ (μ * a ^ 3) ^ ((1 : ℝ) / 2 + ε) := by
      calc (μ * a ^ 3) ^ ((564 : ℝ) / 323)
          = (paramsAt μ a).d ^ (2 * ((paramsAt μ a).M : ℝ) - 2) := hLHS.symm
        _ ≤ (μ * a ^ 3) ^ ((1 : ℝ) / 2) * (μ * a ^ 3) ^ ε := hineq
        _ = (μ * a ^ 3) ^ ((1 : ℝ) / 2 + ε) := by rw [Real.rpow_add ht]
    have hle : (μ * a ^ 3) ^ ((1 : ℝ) / 2 + ε) ≤ (μ * a ^ 3) ^ ((21 : ℝ) / 40) := by
      apply Real.rpow_le_rpow_of_exponent_le h1.le
      have hε : ε ≤ 1 / 40 := by simpa [slack] using hεs
      linarith
    have hfin := (Real.rpow_le_rpow_left_iff h1).mp (le_trans hcmp hle)
    norm_num at hfin
  refine ⟨ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [paramsAt, fsParams] using fsXp_pos (t := μ * a ^ 3) (c := 6) ht
  · simpa only [paramsAt, fsParams] using fsXp_pos (t := μ * a ^ 3) (c := 1) ht
  · simpa only [paramsAt, fsParams] using le_of_lt (fsXp_pos (t := μ * a ^ 3) (c := 23 / 4) ht)
  · simpa only [paramsAt, fsParams]
      using fsXp_le_one (t := μ * a ^ 3) (c := 23 / 4) ht ht1 (by norm_num)
  · simp [paramsAt, fsParams, bValue]
  · simpa only [paramsAt, fsParams] using fsXp_pos (t := μ * a ^ 3) (c := -(3 / 2)) ht

end Work.BoseBox
