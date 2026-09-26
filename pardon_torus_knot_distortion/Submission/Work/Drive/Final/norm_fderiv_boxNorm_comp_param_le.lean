import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.Final

/-- Pardon's box norm `Submission.boxNorm c σ` is `1`-Lipschitz for the Euclidean norm on `ℝ³`.

Indeed `boxNorm c σ y = max_i |y (σ i) - c (σ i)| / boxSide i`, each summand is `1`-Lipschitz
(the coordinate projection is, `abs` is, and `boxSide i ≥ 1`), and the max of two `1`-Lipschitz
functions is `1`-Lipschitz. -/
theorem abs_boxNorm_sub_le (c : R3) (σ : Equiv.Perm (Fin 3)) (z z' : R3) :
    |Submission.boxNorm c σ z - Submission.boxNorm c σ z'| ≤ ‖z - z'‖ := by
  have hA : ∀ i : Fin 3,
      |abs (z (σ i) - c (σ i)) / Submission.boxSide i
       - abs (z' (σ i) - c (σ i)) / Submission.boxSide i| ≤ ‖z - z'‖ := by
    intro i
    have hb : 0 < Submission.boxSide i := Submission.boxSide_pos i
    rw [div_sub_div_same, abs_div, abs_of_pos hb, div_le_iff₀ hb]
    have h2 : |abs (z (σ i) - c (σ i)) - abs (z' (σ i) - c (σ i))| ≤
        |(z (σ i) - c (σ i)) - (z' (σ i) - c (σ i))| := abs_abs_sub_abs_le_abs_sub _ _
    have h3 : (z (σ i) - c (σ i)) - (z' (σ i) - c (σ i)) = z (σ i) - z' (σ i) := by ring
    rw [h3] at h2
    have h4 : |z (σ i) - z' (σ i)| ≤ ‖z - z'‖ := by
      have := PiLp.norm_apply_le (p := 2) (z - z') (σ i)
      simpa [Real.norm_eq_abs] using this
    calc |abs (z (σ i) - c (σ i)) - abs (z' (σ i) - c (σ i))|
        ≤ |z (σ i) - z' (σ i)| := h2
      _ ≤ ‖z - z'‖ := h4
      _ ≤ ‖z - z'‖ * Submission.boxSide i := by
          nth_rewrite 1 [← mul_one ‖z - z'‖]
          exact mul_le_mul_of_nonneg_left (Submission.one_le_boxSide i) (norm_nonneg _)
  rw [show Submission.boxNorm c σ z =
      max (max (|z (σ 0) - c (σ 0)| / Submission.boxSide 0)
               (|z (σ 1) - c (σ 1)| / Submission.boxSide 1))
          (|z (σ 2) - c (σ 2)| / Submission.boxSide 2) from rfl,
    show Submission.boxNorm c σ z' =
      max (max (|z' (σ 0) - c (σ 0)| / Submission.boxSide 0)
               (|z' (σ 1) - c (σ 1)| / Submission.boxSide 1))
          (|z' (σ 2) - c (σ 2)| / Submission.boxSide 2) from rfl]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ (hA 2))
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (hA 0) (hA 1))

/-- The derivative of the pulled-back box norm along the parametrisation `par ψ` is bounded by the
derivative of `par ψ` plus `1`.

Since `boxNorm c σ` is `1`-Lipschitz (`abs_boxNorm_sub_le`) and `par ψ` is `C^∞`, the composite
`boxNorm c σ ∘ par ψ` satisfies `‖boxNorm c σ (par ψ y) − boxNorm c σ (par ψ q)‖ ≤
(‖fderiv (par ψ) q‖ + 1) ‖y − q‖` for `y` close to `q`; the mean-value inequality for derivatives
(`norm_fderiv_le_of_lip'`) then gives the stated bound.  (The `+ 1` absorbs the `o(‖y − q‖)` term in
the differentiability of `par ψ`, and covers the points at which `boxNorm` is not differentiable:
there `fderiv` is `0`.) -/
theorem norm_fderiv_boxNorm_comp_param_le (ψ : Submission.Diffeo)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (q : ℝ × ℝ) :
    ‖fderiv ℝ (fun q' : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q‖ ≤
      ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖ + 1 := by
  have hdiff : DifferentiableAt ℝ (Work.BoxShrink.Pinch.par ψ) q :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)).differentiableAt
  have hlittle := hdiff.hasFDerivAt.isLittleO.bound (show (0 : ℝ) < 1 by norm_num)
  refine norm_fderiv_le_of_lip' ℝ
    (show (0 : ℝ) ≤ ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖ + 1 by positivity) ?_
  filter_upwards [hlittle] with y hy
  rw [Real.norm_eq_abs]
  have h1 : |Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ y)
        - Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)| ≤
      ‖Work.BoxShrink.Pinch.par ψ y - Work.BoxShrink.Pinch.par ψ q‖ :=
    abs_boxNorm_sub_le c σ _ _
  have hpar : ‖Work.BoxShrink.Pinch.par ψ y - Work.BoxShrink.Pinch.par ψ q‖ ≤
      (‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖ + 1) * ‖y - q‖ := by
    have hdecomp : Work.BoxShrink.Pinch.par ψ y - Work.BoxShrink.Pinch.par ψ q =
        (Work.BoxShrink.Pinch.par ψ y - Work.BoxShrink.Pinch.par ψ q
          - (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) (y - q))
        + (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) (y - q) := by abel
    calc ‖Work.BoxShrink.Pinch.par ψ y - Work.BoxShrink.Pinch.par ψ q‖
        = ‖(Work.BoxShrink.Pinch.par ψ y - Work.BoxShrink.Pinch.par ψ q
            - (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) (y - q))
          + (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) (y - q)‖ := by
              conv_lhs => rw [hdecomp]
      _ ≤ ‖Work.BoxShrink.Pinch.par ψ y - Work.BoxShrink.Pinch.par ψ q
            - (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) (y - q)‖
          + ‖(fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) (y - q)‖ := norm_add_le _ _
      _ ≤ 1 * ‖y - q‖ + ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖ * ‖y - q‖ :=
          add_le_add hy (ContinuousLinearMap.le_opNorm _ _)
      _ = (‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖ + 1) * ‖y - q‖ := by ring
  exact h1.trans hpar

end Work.Drive.Final
