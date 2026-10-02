/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.repelling_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Elementary estimates for the branch of the logarithm used by the repelling coordinate

For the repelling coordinate of the parabolic germ `f z = z + z ^ 2 * h z` one uses the
single-valued branch `Λ w = log (-w) + π i` of the logarithm on a left half-plane.  This file
collects the *public* elementary estimates for `Λ` (the corresponding estimates inside
`Repelling/defect_bound` are `private`, so they cannot be reused by the files that build the
flower).

* `norm_Lambda_le_log` — the *sharp* size bound `‖Λ w‖ ≤ log ‖w‖ + 2π` for `1 ≤ ‖w‖`.  This is
  what makes the known decay rate `O((1 + log ‖w‖)/‖w‖²)` of the defect available: the cruder
  bound `‖Λ w‖ ≤ 2 √‖w‖ + 2π` (in `Repelling/defect_lipschitz`) is enough to show that
  `corr a w` is a small fraction of `w`, but not to keep the numerator logarithmic.
* `Lambda_shift_bound` — `Λ (w + 1) - Λ w = 1/w + O(1/‖w‖²)` on `{Re w < -1}`; this is the
  cancellation that the correction `(1 - a) Λ w` is designed for.
* `norm_inv_sub_inv_le` — comparison of reciprocals.
* `exists_lambda_growth` — for every `M ≥ 0` and `t` large, `M (log t + 2π) ≤ t/4`; the form in
  which the logarithmic growth of `Λ` is dominated by the linear factor.
-/

open scoped Topology
open Set Filter Metric

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Flower.LambdaBounds

open Work.FatouCoord Work.FatouCoord.Petal

noncomputable section

/-! ## The sharp size bound for `Λ` -/

/-- On the left half-plane, `‖Λ w‖ ≤ log ‖w‖ + 2π` (for `‖w‖ ≥ 1`): the real part of `Λ w`
is `log ‖w‖` and its imaginary part is `arg (-w) + π ∈ (0, 2π]`. -/
theorem norm_Lambda_le_log {w : ℂ} (h1 : 1 ≤ ‖w‖) :
    ‖Petal.Lambda w‖ ≤ Real.log ‖w‖ + 2 * Real.pi := by
  have hrev : (Petal.Lambda w).re = Real.log ‖w‖ := by simp [Petal.Lambda, Complex.log_re]
  have himv : (Petal.Lambda w).im = (-w).arg + Real.pi := by simp [Petal.Lambda, Complex.log_im]
  have harg := Complex.arg_mem_Ioc (-w)
  rw [Set.mem_Ioc] at harg
  have hlog0 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg h1
  have himabs : |(Petal.Lambda w).im| ≤ 2 * Real.pi := by
    rw [himv, abs_le]; constructor <;> linarith [harg.1, harg.2]
  calc ‖Petal.Lambda w‖ ≤ |(Petal.Lambda w).re| + |(Petal.Lambda w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log ‖w‖ + |(Petal.Lambda w).im| := by rw [hrev, abs_of_nonneg hlog0]
    _ ≤ Real.log ‖w‖ + 2 * Real.pi := by linarith

/-! ## The shift estimate -/

theorem Lambda_shift_bound {w : ℂ} (hre : w.re < -1) (h2 : 2 ≤ ‖w‖) :
    ‖Lambda (w + 1) - Lambda w - 1 / w‖ ≤ 2 / ‖w‖ ^ 2 := by
  have hwn : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) h2
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hwn)
  have hconv_re : Convex ℝ {x : ℂ | x.re ≤ w.re + 1} :=
    (convex_Iic (w.re + 1)).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have hmem_re : ∀ x ∈ segment ℝ w (w + 1), x.re < 0 := by
    intro x hx
    have h1 : w ∈ {x : ℂ | x.re ≤ w.re + 1} := by simp
    have h2' : w + 1 ∈ {x : ℂ | x.re ≤ w.re + 1} := by simp
    have hx' : x.re ≤ w.re + 1 := hconv_re.segment_subset h1 h2' hx
    linarith
  have hmem_norm : ∀ x ∈ segment ℝ w (w + 1), ‖w‖ / 2 ≤ ‖x‖ := by
    intro x hx
    have h1 : w ∈ Metric.closedBall w 1 := by simp
    have h2' : w + 1 ∈ Metric.closedBall w 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; simp
    have hx' := (convex_closedBall w 1).segment_subset h1 h2' hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx'
    have h3 : ‖w‖ ≤ ‖w - x‖ + ‖x‖ := by
      have hh := norm_add_le (w - x) x
      rwa [sub_add_cancel] at hh
    have h4 : ‖w - x‖ ≤ 1 := by rw [norm_sub_rev] at hx'; exact hx'
    linarith
  have hderiv : ∀ x ∈ segment ℝ w (w + 1),
      HasDerivAt (fun y : ℂ => Lambda y - y / w) (1 / x - 1 / w) x := by
    intro x hx
    have hxre : x.re < 0 := hmem_re x hx
    have hxs : -x ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; exact Or.inl (by simpa using hxre)
    have h1 : HasDerivAt Complex.log ((-x)⁻¹) (-x) := Complex.hasDerivAt_log hxs
    have h2d : HasDerivAt (fun y : ℂ => Complex.log (-y)) (((-x)⁻¹) * (-1)) x :=
      h1.comp x (hasDerivAt_neg x)
    have h3 : HasDerivAt Lambda (((-x)⁻¹ * (-1)) + 0) x := by
      have hh := h2d.add_const ((Real.pi : ℂ) * Complex.I)
      convert hh using 1
      · funext y; simp [Lambda]
      · ring
    have h4 : HasDerivAt (fun y : ℂ => y / w) (1 / w) x := (hasDerivAt_id x).div_const w
    have h5 := h3.sub h4
    have hval : ((-x)⁻¹ * (-1) + 0) - 1 / w = 1 / x - 1 / w := by
      have hx0 : x ≠ 0 := by intro h; rw [h] at hxre; simp at hxre
      field_simp
      ring
    rwa [hval] at h5
  have hbnd : ∀ x ∈ segment ℝ w (w + 1),
      ‖deriv (fun y : ℂ => Lambda y - y / w) x‖ ≤ 2 / ‖w‖ ^ 2 := by
    intro x hx
    have hxre : x.re < 0 := hmem_re x hx
    have hxn : ‖w‖ / 2 ≤ ‖x‖ := hmem_norm x hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at hxre; simp at hxre
    have hxn0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    rw [(hderiv x hx).deriv]
    have hxw : ‖w - x‖ ≤ 1 := by
      have h1 : w ∈ Metric.closedBall w 1 := by simp
      have h2' : w + 1 ∈ Metric.closedBall w 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]; simp
      have hx' := (convex_closedBall w 1).segment_subset h1 h2' hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx'
      rwa [norm_sub_rev]
    have heq : (1:ℂ) / x - 1 / w = (w - x) / (x * w) := by
      field_simp
    rw [heq, norm_div, norm_mul]
    have hden : 0 < ‖x‖ * ‖w‖ := mul_pos hxn0 hwn
    have hden2 : 0 < (‖w‖ / 2) * ‖w‖ := by positivity
    calc ‖w - x‖ / (‖x‖ * ‖w‖) ≤ 1 / (‖x‖ * ‖w‖) :=
          div_le_div_of_nonneg_right hxw hden.le
      _ ≤ 1 / ((‖w‖ / 2) * ‖w‖) := by
          apply one_div_le_one_div_of_le hden2
          nlinarith [hxn, hwn]
      _ = 2 / ‖w‖ ^ 2 := by
          rw [show (‖w‖ / 2) * ‖w‖ = ‖w‖ ^ 2 / 2 by ring, one_div_div]
  have hmvt := (convex_segment (𝕜 := ℝ) w (w + 1)).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hderiv x hx).differentiableAt) hbnd
      (left_mem_segment ℝ w (w + 1)) (right_mem_segment ℝ w (w + 1))
  have hww : w / w = 1 := div_self hw0
  rw [hww] at hmvt
  have e : (Lambda (w + 1) - (w + 1) / w) - (Lambda w - 1)
      = Lambda (w + 1) - Lambda w - 1 / w := by
    rw [show (w + 1) / w = 1 + 1 / w by field_simp]; ring
  rw [e] at hmvt
  simpa using hmvt

/-- Comparison of reciprocals: if `‖w‖/2 ≤ ‖V‖` then `‖1/V - 1/w‖ ≤ 2‖V - w‖/‖w‖²`. -/
theorem norm_inv_sub_inv_le {V w : ℂ} (hw : 0 < ‖w‖) (hV : ‖w‖ / 2 ≤ ‖V‖) :
    ‖1 / V - 1 / w‖ ≤ 2 * ‖V - w‖ / ‖w‖ ^ 2 := by
  have hVpos : 0 < ‖V‖ := by linarith
  have hVne : V ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hVpos)
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hw)
  rw [show (1:ℂ) / V - 1 / w = (w - V) / (V * w) by
        field_simp, norm_div, norm_mul]
  rw [div_le_div_iff₀ (mul_pos hVpos hw) (by positivity)]
  rw [norm_sub_rev w V]
  have hdnn : 0 ≤ ‖V - w‖ := norm_nonneg _
  rw [show 2 * ‖V - w‖ * (‖V‖ * ‖w‖) = ‖V - w‖ * (2 * ‖V‖ * ‖w‖) by ring]
  apply mul_le_mul_of_nonneg_left _ hdnn
  have h : ‖w‖ ≤ 2 * ‖V‖ := by linarith
  calc ‖w‖ ^ 2 = ‖w‖ * ‖w‖ := by ring
    _ ≤ (2 * ‖V‖) * ‖w‖ := mul_le_mul_of_nonneg_right h hw.le
    _ = 2 * ‖V‖ * ‖w‖ := by ring


/-! ## The growth threshold -/

/-- For every `M ≥ 0` there is `T` with `M * (log t + 2 * π) ≤ t / 4` for all `t ≥ T`. -/
theorem exists_lambda_growth {M : ℝ} (hM : 0 ≤ M) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → M * (Real.log t + 2 * Real.pi) ≤ t / 4 := by
  have h1 : ∀ᶠ t : ℝ in Filter.atTop, M * Real.log t ≤ t / 8 := by
    have h := Real.isLittleO_log_id_atTop.const_mul_left (8 * M)
    filter_upwards [h.eventuallyLE, Filter.eventually_ge_atTop (0 : ℝ)] with t ht ht0
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg ht0, abs_mul, abs_of_nonneg hM,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 8)] at ht
    have h3 : M * Real.log t ≤ M * |Real.log t| := mul_le_mul_of_nonneg_left (le_abs_self _) hM
    linarith
  have h2 : ∀ᶠ t : ℝ in Filter.atTop, M * (2 * Real.pi) ≤ t / 8 := by
    have h0 : 0 ≤ M * (2 * Real.pi) := mul_nonneg hM (by positivity)
    filter_upwards [Filter.eventually_ge_atTop (16 * (M * (2 * Real.pi)))] with t ht
    linarith
  have hmain : ∀ᶠ t : ℝ in Filter.atTop, M * (Real.log t + 2 * Real.pi) ≤ t / 4 := by
    filter_upwards [h1, h2] with t ht1 ht2
    have e : M * (Real.log t + 2 * Real.pi) = M * Real.log t + M * (2 * Real.pi) := by ring
    rw [e]; linarith
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hmain
  exact ⟨T, fun t ht => hT t ht⟩

end

end Work.FatouCoord.Flower.LambdaBounds
