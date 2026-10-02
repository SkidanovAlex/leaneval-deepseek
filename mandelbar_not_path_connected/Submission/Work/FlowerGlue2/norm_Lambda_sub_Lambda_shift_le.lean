import Mathlib
import Submission.Work.FatouCoord.Repelling.defect_lipschitz
import Submission.Work.FatouCoord.Flower.exists_threshold_log_div
import Submission.Work.FatouCoord.Repelling.norm_Lambda_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The branch `Λ` is Hölder with constant `2/‖w‖` along the shift `w ↦ w - (1-a) Λ w`

The repelling coordinate of the parabolic germ is built from the single-valued branch
`Λ w = log (-w) + π i` of the logarithm on the left half-plane
(`Work.FatouCoord.Petal.Lambda`).  The correction `(1 - a) * Λ w` shifts `w` by a quantity of
size `O(log ‖w‖)`, which is *small compared to* `w`: consequently

  `Λ (w - (1-a) Λ w) - Λ w = O(‖1-a‖ (1 + log ‖w‖)/‖w‖)`

uniformly on the deep left half-plane.  This is the "logarithmic shift" estimate consumed by the
flower-gluing comparison of the mandelbar implosion.

## The proof

`Λ` is a primitive of `u ↦ 1/u` on the cut plane `ℂ ∖ [0,∞)` (`-u ∈ slitPlane`).  The two points
`w` and `v = w - (1-a) Λ w` are joined by a segment which stays at distance `≤ ‖w‖/8` from `w`,
and such a segment never meets the cut: either `|w.re| ≥ ‖w‖/4` (the segment stays in the left
half-plane) or `|w.im| > ‖w‖/8` (the segment stays off the real axis).  The mean value inequality
with the derivative bound `‖1/u‖ ≤ 2/‖w‖` on that segment gives the claim.

## Main result

* `Work.FlowerGlue2.norm_Lambda_sub_Lambda_shift_le`
-/

open Set Metric

namespace Work.FlowerGlue2

noncomputable section

/-- On the half-plane `1 ≤ ‖w‖` the branch `Λ w = log (-w) + π i` satisfies
`‖Λ w‖ ≤ log ‖w‖ + 2π`: its real part is `log ‖w‖` and its imaginary part is
`arg (-w) + π ∈ (0, 2π]`. -/
private lemma norm_Lambda_le_log_real {w : ℂ} (h1 : 1 ≤ ‖w‖) :
    ‖Work.FatouCoord.Petal.Lambda w‖ ≤ Real.log ‖w‖ + 2 * Real.pi := by
  have hrev : (Work.FatouCoord.Petal.Lambda w).re = Real.log ‖w‖ := by
    simp [Work.FatouCoord.Petal.Lambda, Complex.log_re]
  have himv : (Work.FatouCoord.Petal.Lambda w).im = (-w).arg + Real.pi := by
    simp [Work.FatouCoord.Petal.Lambda, Complex.log_im]
  have harg := Complex.arg_mem_Ioc (-w)
  rw [Set.mem_Ioc] at harg
  have hlog0 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg h1
  have himabs : |(Work.FatouCoord.Petal.Lambda w).im| ≤ 2 * Real.pi := by
    rw [himv, abs_le]
    constructor
    · linarith [harg.1]
    · linarith [harg.2]
  calc ‖Work.FatouCoord.Petal.Lambda w‖
      ≤ |(Work.FatouCoord.Petal.Lambda w).re| + |(Work.FatouCoord.Petal.Lambda w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log ‖w‖ + |(Work.FatouCoord.Petal.Lambda w).im| := by
        rw [hrev, abs_of_nonneg hlog0]
    _ ≤ Real.log ‖w‖ + 2 * Real.pi := by linarith

/-- Every point of the ball of radius `‖w‖/8` about a point `w` of the open left half-plane lies
off the cut `[0, ∞)`: more precisely `-u ∈ slitPlane`, so that `u ↦ log (-u)` is complex
differentiable at `u`.

Indeed, if `|w.re| ≥ ‖w‖/4` the whole ball is contained in `{Re < 0}`; otherwise `|w.im| > ‖w‖/8`
and the whole ball is contained in `{Im ≠ 0}`. -/
private lemma neg_mem_slitPlane {w u : ℂ} (hw : w.re < 0) (hu : ‖u - w‖ ≤ ‖w‖ / 8) :
    -u ∈ Complex.slitPlane := by
  have hwn : 0 < ‖w‖ := by
    rw [norm_pos_iff]
    intro h0
    rw [h0] at hw
    simp at hw
  rw [Complex.mem_slitPlane_iff]
  have hre : |u.re - w.re| ≤ ‖w‖ / 8 := by
    have h := Complex.abs_re_le_norm (u - w)
    rw [Complex.sub_re] at h
    exact le_trans h hu
  have him : |u.im - w.im| ≤ ‖w‖ / 8 := by
    have h := Complex.abs_im_le_norm (u - w)
    rw [Complex.sub_im] at h
    exact le_trans h hu
  rcases lt_or_ge |w.re| (‖w‖ / 4) with hcase | hcase
  · -- the imaginary part is large: the whole ball is contained in `{Im ≠ 0}`
    right
    rw [Complex.neg_im]
    intro hzero
    have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hre2 : w.re ^ 2 < (‖w‖ / 4) ^ 2 := by
      rw [sq_lt_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ / 4)]
      exact hcase
    have hwim : ‖w‖ / 8 < |w.im| := by
      have hsq' : (‖w‖ / 8) ^ 2 < w.im ^ 2 := by nlinarith [hsq, hre2, hwn]
      rwa [sq_lt_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w‖ / 8)] at hsq'
    have himu : |w.im| - |u.im - w.im| ≤ |u.im| := by
      have h := abs_add_le u.im (w.im - u.im)
      rw [show u.im + (w.im - u.im) = w.im by ring] at h
      rw [← abs_sub_comm u.im w.im] at h
      linarith
    have hpos : 0 < |u.im| := by linarith
    rw [abs_pos] at hpos
    exact hpos (by linarith)
  · -- the real part is far to the left: the whole ball lies in the left half-plane
    left
    rw [Complex.neg_re]
    have h1 : u.re ≤ w.re + ‖w‖ / 8 := by
      have h := (abs_le.mp hre).2
      linarith
    have h2 : w.re = -|w.re| := by
      rw [abs_of_neg hw]
      ring
    linarith

theorem norm_Lambda_sub_Lambda_shift_le {a : ℂ} (ha : a.re < 1) :
    ∃ T : ℝ, 0 < T ∧ ∀ w : ℂ, w.re < -T →
      ‖Work.FatouCoord.Petal.Lambda (w - (1 - a) * Work.FatouCoord.Petal.Lambda w)
        - Work.FatouCoord.Petal.Lambda w‖ ≤
        8 * ‖1 - a‖ * (1 + Real.log ‖w‖) / ‖w‖ := by
  -- the threshold from `C (log t + 2π) ≤ t/16` for `C = ‖1 - a‖`
  obtain ⟨T₁, hT₁pos, hT₁⟩ :=
    Work.FatouCoord.Flower.exists_threshold_log_div (8 * ‖1 - a‖)
  set T : ℝ := max T₁ (max (Real.exp (4 * Real.pi)) 3) with hT
  have hTpos : 0 < T := by
    rw [hT]
    exact lt_max_iff.mpr (Or.inl hT₁pos)
  refine ⟨T, hTpos, ?_⟩
  intro w hw
  have hT₁le : T₁ ≤ T := by rw [hT]; exact le_max_left _ _
  have hexp_le : Real.exp (4 * Real.pi) ≤ T := by
    rw [hT]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h3le : (3 : ℝ) ≤ T := by
    rw [hT]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hwre : w.re < 0 := by linarith
  have hnorm_gt : T < ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    rw [abs_of_neg hwre] at h
    linarith
  have hwT₁ : T₁ ≤ ‖w‖ := le_of_lt (lt_of_le_of_lt hT₁le hnorm_gt)
  have hw_exp : Real.exp (4 * Real.pi) ≤ ‖w‖ :=
    le_of_lt (lt_of_le_of_lt hexp_le hnorm_gt)
  have hwn : 0 < ‖w‖ := lt_of_lt_of_le (Real.exp_pos _) hw_exp
  have hnorm1 : (1 : ℝ) ≤ ‖w‖ := by
    have h := le_of_lt (lt_of_le_of_lt h3le hnorm_gt)
    linarith
  have hlog4pi : 4 * Real.pi ≤ Real.log ‖w‖ := by
    have h := Real.log_le_log (Real.exp_pos (4 * Real.pi)) hw_exp
    rwa [Real.log_exp] at h
  -- the size of the branch on the deep half-plane
  have hLam : ‖Work.FatouCoord.Petal.Lambda w‖ ≤ Real.log ‖w‖ + 2 * Real.pi :=
    norm_Lambda_le_log_real hnorm1
  set v : ℂ := w - (1 - a) * Work.FatouCoord.Petal.Lambda w with hv
  -- the shift is short compared with `w`
  have hd : ‖v - w‖ ≤ ‖1 - a‖ * (Real.log ‖w‖ + 2 * Real.pi) := by
    have he : v - w = -((1 - a) * Work.FatouCoord.Petal.Lambda w) := by
      rw [hv]; ring
    rw [he, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_left hLam (norm_nonneg _)
  have hd8 : ‖v - w‖ ≤ ‖w‖ / 8 := by
    have hthr := hT₁ ‖w‖ hwT₁
    have hCnn : 0 ≤ ‖1 - a‖ := norm_nonneg _
    nlinarith [hd, hthr, hCnn, hwn]
  -- the segment joining `w` to `v` avoids the cut
  have hseg : ∀ x ∈ segment ℝ w v, -x ∈ Complex.slitPlane := by
    intro x hx
    have hvmem : v ∈ Metric.closedBall w (‖w‖ / 8) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hd8
    have hxmem := (convex_closedBall w (‖w‖ / 8)).segment_subset
      (Metric.mem_closedBall_self (by positivity)) hvmem hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hxmem
    exact neg_mem_slitPlane hwre hxmem
  have hdiff : ∀ x ∈ segment ℝ w v,
      DifferentiableAt ℂ (fun y : ℂ => Complex.log (-y)) x := by
    intro x hx
    exact ((Complex.hasDerivAt_log (hseg x hx)).comp x (hasDerivAt_neg x)).differentiableAt
  -- the derivative bound `‖1/u‖ ≤ 2/‖w‖` on the segment
  have hbnd : ∀ x ∈ segment ℝ w v,
      ‖deriv (fun y : ℂ => Complex.log (-y)) x‖ ≤ 2 / ‖w‖ := by
    intro x hx
    have hvmem : v ∈ Metric.closedBall w (‖w‖ / 8) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hd8
    have hxmem := (convex_closedBall w (‖w‖ / 8)).segment_subset
      (Metric.mem_closedBall_self (by positivity)) hvmem hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hxmem
    have hxn : ‖w‖ / 2 ≤ ‖x‖ := by
      have h := (abs_le.mp (abs_norm_sub_norm_le w x)).2
      rw [norm_sub_rev] at h
      linarith
    have hde : deriv (fun y : ℂ => Complex.log (-y)) x = x⁻¹ := by
      have h1 : deriv (fun y : ℂ => Complex.log (-y)) x = (-x)⁻¹ * (-1) :=
        ((Complex.hasDerivAt_log (hseg x hx)).comp x (hasDerivAt_neg x)).deriv
      rw [h1, inv_neg]
      ring
    rw [hde, norm_inv]
    have h1 : 1 / ‖x‖ ≤ 1 / (‖w‖ / 2) := one_div_le_one_div_of_le (by positivity) hxn
    have h2 : 1 / (‖w‖ / 2) = 2 / ‖w‖ := one_div_div ‖w‖ 2
    calc ‖x‖⁻¹ = 1 / ‖x‖ := (one_div _).symm
      _ ≤ 1 / (‖w‖ / 2) := h1
      _ = 2 / ‖w‖ := h2
  -- mean value inequality on the segment
  have hmvt := (convex_segment (𝕜 := ℝ) w v).norm_image_sub_le_of_norm_deriv_le
    hdiff hbnd (left_mem_segment ℝ w v) (right_mem_segment ℝ w v)
  have hlogbound : Real.log ‖w‖ + 2 * Real.pi ≤ 4 * (1 + Real.log ‖w‖) := by
    linarith [hlog4pi, Real.pi_pos]
  have hkey : Work.FatouCoord.Petal.Lambda v - Work.FatouCoord.Petal.Lambda w
      = Complex.log (-v) - Complex.log (-w) := by
    simp only [Work.FatouCoord.Petal.Lambda]
    ring
  calc ‖Work.FatouCoord.Petal.Lambda v - Work.FatouCoord.Petal.Lambda w‖
      = ‖Complex.log (-v) - Complex.log (-w)‖ := by rw [hkey]
    _ ≤ (2 / ‖w‖) * ‖v - w‖ := hmvt
    _ ≤ (2 / ‖w‖) * (‖1 - a‖ * (Real.log ‖w‖ + 2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hd (div_nonneg (by norm_num) hwn.le)
    _ ≤ (2 / ‖w‖) * (‖1 - a‖ * (4 * (1 + Real.log ‖w‖))) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) hwn.le)
        exact mul_le_mul_of_nonneg_left hlogbound (norm_nonneg _)
    _ = 8 * ‖1 - a‖ * (1 + Real.log ‖w‖) / ‖w‖ := by ring

end

end Work.FlowerGlue2
