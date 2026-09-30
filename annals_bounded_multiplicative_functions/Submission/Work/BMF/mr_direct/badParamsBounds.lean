import Mathlib
import Submission.Work.BMF.mr_direct.badDefs
import Submission.Work.BMF.mr_direct.le_log_div_loglog_of_large
import Submission.Work.BMF.mr_direct.badQ_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The admissible range of the bad-set parameters

The bad-set stage of `Work.BMF.MRDirichletL2Direct` runs at the scales

* `Q = badQ Y = exp(log Y / log log Y)`,
* `P = badP a Y = Q ^ a`, with `a ∈ (0, 1/2]` fixed,

and every downstream estimate is applied only for `Y` beyond an explicit threshold.  This file
records the (purely numerical) admissibility statement: for every tolerance `ε' > 0` and every
`a ∈ (0,1/2]` there is `X₀ ≥ 1` such that for all `Y ≥ X₀`

* `Y ≥ 16`, `log Y > 1`, `log log Y > 1` (so the exponent `R = log Y / log log Y` is `> 0`),
* `2 ≤ P ≤ Q`, `Q ≥ 1`, `log Q ≤ log Y`,
* `1/P ≤ ε'/120`.

The single analytic input is `log Y / log log Y → ∞` (the two scales are `exp(o(log Y))`); the
rest is `exp`/`rpow` bookkeeping.  Note `P ≥ 2` and `1/P ≤ ε'/120` are the two conditions that
force `X₀` to depend on `a` and `ε'`, while `a ≤ 1` is what gives `P ≤ Q`.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- Admissibility of the bad-set parameters: for `a ∈ (0,1/2]` and `ε' > 0`, all model
hypotheses on `Y` hold for all large `Y`. -/
theorem badParamsBounds :
    ∀ ε' : ℝ, 0 < ε' → ∀ a : ℝ, 0 < a → a ≤ 1 / 2 →
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ Y : ℝ, X₀ ≤ Y →
      (16 : ℝ) ≤ Y ∧ (1 : ℝ) < Real.log Y ∧ (1 : ℝ) < Real.log (Real.log Y) ∧
      (2 : ℝ) ≤ Work.BMF.mr_direct.badP a Y ∧
      Work.BMF.mr_direct.badP a Y ≤ Work.BMF.mr_direct.badQ Y ∧
      (1 : ℝ) ≤ Work.BMF.mr_direct.badQ Y ∧
      Real.log (Work.BMF.mr_direct.badQ Y) ≤ Real.log Y ∧
      1 / Work.BMF.mr_direct.badP a Y ≤ ε' / 120 := by
  intro ε' hε' a ha0 ha1
  -- The target size `C` that `badP a Y` has to exceed, and the resulting exponent threshold.
  set C : ℝ := max 2 (120 / ε') with hC
  have hC2 : (2 : ℝ) ≤ C := by rw [hC]; exact le_max_left _ _
  have hC120 : 120 / ε' ≤ C := by rw [hC]; exact le_max_right _ _
  have hC1 : (1 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC2
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  have hlogCpos : 0 < Real.log C := Real.log_pos hC1
  set K : ℝ := Real.log C / a with hK
  have hKpos : 0 < K := div_pos hlogCpos ha0
  -- `log Y / log log Y → ∞`, hence `R ≥ K` for all large `Y`.
  obtain ⟨X, _hX1, hX⟩ := le_log_div_loglog_of_large K hKpos
  refine ⟨max (max X 16) (Real.exp (Real.exp 2)), ?_, ?_⟩
  · exact le_trans (le_trans (by norm_num) (le_max_right X 16)) (le_max_left _ _)
  · intro Y hY
    have hYX : X ≤ Y := le_trans (le_trans (le_max_left X 16) (le_max_left _ _)) hY
    have hY16 : (16 : ℝ) ≤ Y := le_trans (le_trans (le_max_right X 16) (le_max_left _ _)) hY
    have hYee : Real.exp (Real.exp 2) ≤ Y := le_trans (le_max_right _ _) hY
    -- `log Y ≥ exp 2`, so `log Y > 1` and `log log Y ≥ 2 > 1`.
    have hexp2_le_s : Real.exp 2 ≤ Real.log Y := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp 2)) hYee
      rwa [Real.log_exp] at h
    have hexp2gt1 : (1 : ℝ) < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    have hlogY_gt1 : (1 : ℝ) < Real.log Y := lt_of_lt_of_le hexp2gt1 hexp2_le_s
    have hv_ge2 : (2 : ℝ) ≤ Real.log (Real.log Y) := by
      have h := Real.log_le_log (Real.exp_pos 2) hexp2_le_s
      rwa [Real.log_exp] at h
    have hloglog_gt1 : (1 : ℝ) < Real.log (Real.log Y) := lt_of_lt_of_le (by norm_num) hv_ge2
    have hK_le_R : K ≤ Real.log Y / Real.log (Real.log Y) := hX Y hYX
    -- `badP a Y = exp (a * (log Y / log log Y))`.
    have hbadP : Work.BMF.mr_direct.badP a Y =
        Real.exp (a * (Real.log Y / Real.log (Real.log Y))) := by
      unfold Work.BMF.mr_direct.badP Work.BMF.mr_direct.badQ
      rw [Real.rpow_def_of_pos (Real.exp_pos (Real.log Y / Real.log (Real.log Y))) a,
        Real.log_exp]
      congr 1
      ring
    have haK : a * K = Real.log C := by rw [hK]; field_simp
    have haR_ge : Real.log C ≤ a * (Real.log Y / Real.log (Real.log Y)) := by
      have h := mul_le_mul_of_nonneg_left hK_le_R (le_of_lt ha0)
      rwa [haK] at h
    have hbadP_ge_C : C ≤ Work.BMF.mr_direct.badP a Y := by
      rw [hbadP]
      calc C = Real.exp (Real.log C) := (Real.exp_log hCpos).symm
        _ ≤ Real.exp (a * (Real.log Y / Real.log (Real.log Y))) := Real.exp_le_exp.mpr haR_ge
    have h2le : (2 : ℝ) ≤ Work.BMF.mr_direct.badP a Y := le_trans hC2 hbadP_ge_C
    -- The structural relations between `badP` and `badQ`.
    obtain ⟨hbadQ1, hbadPle, hlogbadQ⟩ :=
      badQ_bounds (a := a) (Y := Y) (by linarith) (le_of_lt hlogY_gt1) (le_of_lt hloglog_gt1)
    have hbadP_ge_120 : 120 / ε' ≤ Work.BMF.mr_direct.badP a Y := le_trans hC120 hbadP_ge_C
    have h120pos : 0 < 120 / ε' := div_pos (by norm_num) hε'
    have hinv := one_div_le_one_div_of_le h120pos hbadP_ge_120
    rw [one_div_div] at hinv
    exact ⟨hY16, hlogY_gt1, hloglog_gt1, h2le, hbadPle, hbadQ1, hlogbadQ, hinv⟩

end

end Work.BMF.mr_direct
