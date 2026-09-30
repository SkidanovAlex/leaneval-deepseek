import Mathlib
import Submission.Work.BMF.ztw_defs
import Submission.Work.BMF.ztw_asym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N7

open Filter
open scoped Real Topology

/-- The truncation conjunct (conjunct 4) of the `6/7`-shaped twisted Perron parameter package: `twT L u ≥ L^2 exp(L^{1/10})` (lemma `le_twT`) gives `exp L * L^2 / twT L u ≤ exp(L - L^{1/10})`, and `L^(1/10) - (κ/16)L^(1/12) → ∞` beats the constant `Ctr`; `ztw_rpow_mul_exp_sub_le` in `Submission/Work/BMF/ztw_asym.lean` is exactly the shape needed. The hypothesis `|u| ≤ exp(L^{21/20})` is not needed. -/
theorem ztw_truncN7 (κ Ctr : ℝ) (hκ : 0 < κ) (hCtr : 0 < Ctr) : ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (21 / 20 : ℝ)) → Ctr * (Real.exp L * L ^ 2 / Work.BMF.twT L u + L) ≤ (1 / 8) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
  have hc : 0 < κ / 16 := by positivity
  -- The two eventual domination statements obtained from the asymptotic helper
  -- `ztw_rpow_mul_exp_sub_le`, i.e. `L^{1/10}` dominates `(κ/16) L^{1/12}` and the
  -- constant `Ctr`, both in the exponentiated form.
  have hstep1 : ∀ᶠ L : ℝ in Filter.atTop,
      Ctr ≤ (1 / 256 : ℝ) * Real.exp (L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ)) := by
    have h := Work.BMF.ztw_rpow_mul_exp_sub_le (16 * Ctr) 0 1 (κ / 16) (1 / 10) (1 / 12) (1 / 16)
      (by positivity) one_pos hc.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [h] with L hL
    rw [Real.rpow_zero, mul_one, one_mul, Real.exp_neg] at hL
    have hE : 0 < Real.exp (L ^ (1 / 10 : ℝ) - κ / 16 * L ^ (1 / 12 : ℝ)) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hL hE.le
    rw [mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero _), mul_one] at hmul
    linarith
  have hstep2 : ∀ᶠ L : ℝ in Filter.atTop,
      Ctr * L ≤ (1 / 16 : ℝ) * Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := by
    have h := Work.BMF.ztw_rpow_mul_exp_sub_le (16 * Ctr) 1 1 (κ / 16) 1 (1 / 12) (1 / 16)
      (by positivity) one_pos hc.le one_pos (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [h] with L hL
    rw [Real.rpow_one, one_mul, Real.exp_neg] at hL
    have hE : 0 < Real.exp (L - κ / 16 * L ^ (1 / 12 : ℝ)) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hL hE.le
    rw [mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero _), mul_one] at hmul
    linarith
  filter_upwards [hstep1, hstep2, eventually_gt_atTop (0 : ℝ)] with L hs1 hs2 hLpos
  intro u hu
  -- The truncation term: `twT L u ≥ L^2 exp(L^{1/10})`.
  have hT : L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) ≤ Work.BMF.twT L u := Work.BMF.le_twT L u
  have hApos : 0 < L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) := by positivity
  have hX : Real.exp L * L ^ 2 / Work.BMF.twT L u ≤ Real.exp (L - L ^ (1 / 10 : ℝ)) := by
    have h1 : Real.exp L * L ^ 2 / Work.BMF.twT L u ≤
        Real.exp L * L ^ 2 / (L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) hApos hT
    have h2 : Real.exp L * L ^ 2 / (L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ))) =
        Real.exp (L - L ^ (1 / 10 : ℝ)) := by
      rw [Real.exp_sub]; field_simp
    linarith [h1, h2.le]
  -- First summand is absorbed by `(1/16) exp (L - (κ/16) L^{1/12})`.
  have hterm1 : Ctr * (Real.exp L * L ^ 2 / Work.BMF.twT L u) ≤
      (1 / 16) * Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := by
    have h1 : Ctr * (Real.exp L * L ^ 2 / Work.BMF.twT L u) ≤
        Ctr * Real.exp (L - L ^ (1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hX hCtr.le
    have h2 : Ctr * Real.exp (L - L ^ (1 / 10 : ℝ)) ≤
        (1 / 16) * Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := by
      have h3 := mul_le_mul_of_nonneg_right hs1 (Real.exp_pos (L - L ^ (1 / 10 : ℝ))).le
      have he : (1 / 256 : ℝ) * Real.exp (L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ)) *
                  Real.exp (L - L ^ (1 / 10 : ℝ)) =
              (1 / 256 : ℝ) * Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add,
            show (L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ)) + (L - L ^ (1 / 10 : ℝ)) =
              L - (κ / 16) * L ^ (1 / 12 : ℝ) from by ring]
      rw [he] at h3
      have hXp : 0 < Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := Real.exp_pos _
      linarith
    linarith
  -- The exponential `exp (L - c L^{1/12})` in the product form of the goal.
  have key : Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) =
      Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by
    rw [Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
  rw [mul_add]
  rw [key] at hterm1 hs2
  linarith

end Work.BMF.N7
