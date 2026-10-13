/-
# `Work.CoreResiduals.BiotSavart.norm_resid_le_far` — the far-field bound for the kernel
Taylor residual

The far-field `C^{1,1}` estimate for the Biot–Savart field needs a bound on the *second-order*
Taylor residual of the Newtonian kernel `kf b = ‖b‖⁻³ • b`:

  `resid h y = kf (y + h) - kf y - kDerivCLM y h`

which is quadratic in `‖h‖` and homogeneous of degree `-4` in `‖y‖` as soon as the increment is
small compared to `‖y‖` (`2‖h‖ ≤ ‖y‖`).  Concretely this file proves

  `‖resid h y‖ ≤ 1024 ‖h‖² ‖y‖^{-4}`   whenever  `2‖h‖ ≤ ‖y‖`.

The proof is the mean value theorem applied to the difference of the derivative:

* the derivative of `b ↦ kf b` is `kDerivCLM b`, and on the segment `[y, y+h]` every point `x`
  satisfies `‖x‖ ≥ ‖y‖/2` (because `‖x - y‖ ≤ ‖h‖ ≤ ‖y‖/2`), so the Lipschitz bound
  `‖kDerivCLM x - kDerivCLM y‖ ≤ 64 / m⁴ * ‖x - y‖` of
  `Work.StabilityFar.Decay.norm_kDerivCLM_sub_le` is available with `m = ‖y‖/2`;
* the mean value inequality with a subtracted linear map
  (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`) turns this into
  `‖kf (y+h) - kf y - kDerivCLM y h‖ ≤ (64 / (‖y‖/2)⁴ * ‖h‖) * ‖h‖`, and
  `64 / (‖y‖/2)⁴ = 1024 / ‖y‖⁴`.

The two elementary ingredients are isolated below in full generality
(`half_norm_le_norm_of_mem_segment` and `norm_taylor_second_le`); the constant `1024 = 64 · 2⁴` is
exactly the `1/m⁴` Lipschitz constant at `m = ‖y‖/2`.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.kf_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay (kf kDerivCLM)

/-! ## Two general ingredients -/

/-- **The far part of a small segment stays away from the origin.**  If `2‖h‖ ≤ ‖y‖` then every
point `x` of the segment `[y, y+h]` satisfies `‖y‖/2 ≤ ‖x‖`. -/
lemma half_norm_le_norm_of_mem_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y h x : E} (hy : 2 * ‖h‖ ≤ ‖y‖) (hx : x ∈ segment ℝ y (y + h)) : ‖y‖ / 2 ≤ ‖x‖ := by
  have hsub : ‖x - y‖ ≤ ‖h‖ := by
    have := norm_sub_le_of_mem_segment (x := y) (z := y + h) hx
    simpa using this
  have hsplit : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    have := norm_add_le (y - x) x
    simpa using this
  rw [norm_sub_rev] at hsplit
  linarith

/-- **Second-order Taylor estimate from a Lipschitz bound on the derivative.**  If `f` is
differentiable on the segment `[y, y+h]` with derivative `f'`, and `f'` is `L`-Lipschitz on that
segment (`‖f' x - f' y‖ ≤ L ‖x - y‖`, `L ≥ 0`), then the Taylor residual of order two is
quadratic:

  `‖f (y + h) - f y - f' y h‖ ≤ L ‖h‖²`.

This is the mean value inequality with the subtracted linear map `f' y`. -/
lemma norm_taylor_second_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E → E →L[ℝ] F} {y h : E} {L : ℝ} (hL : 0 ≤ L)
    (hdiff : ∀ x ∈ segment ℝ y (y + h), HasFDerivWithinAt f (f' x) (segment ℝ y (y + h)) x)
    (hlip : ∀ x ∈ segment ℝ y (y + h), ‖f' x - f' y‖ ≤ L * ‖x - y‖) :
    ‖f (y + h) - f y - f' y h‖ ≤ L * ‖h‖ ^ 2 := by
  have hmain := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := f) (f' := f') (φ := f' y) (C := L * ‖h‖) (s := segment ℝ y (y + h))
      (x := y) (y := y + h) hdiff
      (fun x hx => by
        have hb : ‖x - y‖ ≤ ‖h‖ := by
          have := norm_sub_le_of_mem_segment (x := y) (z := y + h) hx
          simpa using this
        calc ‖f' x - f' y‖ ≤ L * ‖x - y‖ := hlip x hx
          _ ≤ L * ‖h‖ := by gcongr)
      (convex_segment y (y + h)) (left_mem_segment ℝ y (y + h)) (right_mem_segment ℝ y (y + h))
  simpa [add_sub_cancel_left, pow_two, mul_assoc] using hmain

/-! ## The far-field bound for the kernel residual -/

/-- **Far-field bound for the second-order Taylor residual of the Newtonian kernel.**  If the
increment is small compared with the base point (`2‖h‖ ≤ ‖y‖`), then

  `‖resid h y‖ ≤ 1024 ‖h‖² ‖y‖^{-4}`.

The constant comes from `‖kDerivCLM x - kDerivCLM y‖ ≤ 64 (‖y‖/2)⁻⁴ ‖x - y‖` on the segment. -/
theorem norm_resid_le_far (h y : Work.LWP.R3) (hy : 2 * ‖h‖ ≤ ‖y‖) :
    ‖Work.CoreResiduals.BiotSavart.resid h y‖ ≤ 1024 * ‖h‖ ^ (2:ℕ) * ‖y‖ ^ (-4:ℝ) := by
  by_cases hh : h = 0
  · subst hh
    simp [Work.CoreResiduals.BiotSavart.resid]
  · have hposh : 0 < ‖h‖ := norm_pos_iff.mpr hh
    have hposy : 0 < ‖y‖ := by linarith
    have hhalf : ∀ x ∈ segment ℝ y (y + h), ‖y‖ / 2 ≤ ‖x‖ :=
      fun x hx => half_norm_le_norm_of_mem_segment hy hx
    -- the kernel is differentiable on the segment, since `0` is at distance `‖y‖/2` from it
    have hdiff : ∀ x ∈ segment ℝ y (y + h),
        HasFDerivWithinAt kf (kDerivCLM x) (segment ℝ y (y + h)) x := by
      intro x hx
      have hx0 : x ≠ 0 := by
        have h1 : 0 < ‖y‖ / 2 := by linarith
        exact norm_pos_iff.mp (by linarith [hhalf x hx])
      exact (Work.StabilityFar.Decay.kf_hasFDerivAt x hx0).hasFDerivWithinAt
    -- the derivative is `64 (‖y‖/2)⁻⁴`-Lipschitz on the segment
    have hlip : ∀ x ∈ segment ℝ y (y + h),
        ‖kDerivCLM x - kDerivCLM y‖ ≤ 64 / (‖y‖ / 2) ^ 4 * ‖x - y‖ := by
      intro x hx
      exact Work.StabilityFar.Decay.norm_kDerivCLM_sub_le x y (‖y‖ / 2) (by linarith)
        (hhalf x hx) (by linarith)
    have hkey : ‖Work.CoreResiduals.BiotSavart.resid h y‖
        ≤ 64 / (‖y‖ / 2) ^ 4 * ‖h‖ ^ 2 :=
      norm_taylor_second_le (by positivity) hdiff hlip
    refine hkey.trans_eq ?_
    have h64 : (64:ℝ) / (‖y‖ / 2) ^ 4 = 1024 / ‖y‖ ^ 4 := by
      field_simp
      ring
    rw [h64, div_eq_mul_inv,
      Work.CoreResiduals.BiotSavart.inv_natPow_eq_rpow_neg ‖y‖ (norm_nonneg y) 4]
    ring_nf

end Work.CoreResiduals.BiotSavart
