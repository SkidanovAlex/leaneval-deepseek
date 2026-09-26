import Mathlib

set_option linter.unusedVariables false

namespace Work.Smooth.BoxGeneric.LocalArc

open Set

/-- **Sign and monotonicity from derivative bounds.**

Let `F : ℝ × ℝ → ℝ` be `C¹` with `F 0 = 0` and `fderiv ℝ F 0 z = a z₁ + b z₂`, `a > 0`.
Assume that on the ball `‖q‖ ≤ Rx` (the norm on `ℝ × ℝ` being the *sup* norm, so this ball
contains the box `[-Rx,Rx] × [-Ry,Ry]`) the derivative of `F` is within `a/4` of its value at the
origin, and that `|b| Ry < (3a/4) Rx`.

Then `F` is negative on the left face `x = -Rx` and positive on the right face `x = Rx` of the box
`[-Rx,Rx] × [-Ry,Ry]`, and every slice `x ↦ F (x, y)` (`|y| ≤ Ry`) is strictly increasing on
`[-Rx,Rx]`.

The proof is the mean value inequality: `F` is uniformly close to the affine model
`q ↦ a q₁ + b q₂` on the ball, and the `x`-coefficient `a` dominates the (possible) drift `b y`
because `‖q‖ ≤ Rx` makes `F (Rx, y)` differ from `a Rx + b y` by at most `(a/4) Rx`. -/
theorem sign_and_mono_of_deriv_bounds {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    {a b Rx Ry : ℝ} (ha : 0 < a) (hRx : 0 < Rx) (hRy : 0 < Ry) (hRyRx : Ry ≤ Rx)
    (hder : ∀ z : ℝ × ℝ, fderiv ℝ F 0 z = a * z.1 + b * z.2)
    (hb : |b| * Ry < (3 * a / 4) * Rx)
    (hclose : ∀ q : ℝ × ℝ, ‖q‖ ≤ Rx → ‖fderiv ℝ F q - fderiv ℝ F 0‖ ≤ a / 4) :
    (∀ y : ℝ, |y| ≤ Ry → F (-Rx, y) < 0 ∧ 0 < F (Rx, y)) ∧
    (∀ y : ℝ, |y| ≤ Ry → StrictMonoOn (fun x : ℝ => F (x, y)) (Set.Icc (-Rx) Rx)) := by
  have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  -- The norm of a pair is the maximum of the norms of its components.
  have norm_pair : ∀ u v : ℝ, ‖((u, v) : ℝ × ℝ)‖ = max |u| |v| := by
    intro u v
    simp only [Prod.norm_def, Real.norm_eq_abs]
  -- Mean value inequality: `F` is uniformly close to the affine model on the ball of radius `Rx`.
  have hmvt : ∀ x y : ℝ × ℝ, ‖x‖ ≤ Rx → ‖y‖ ≤ Rx →
      ‖F y - F x - fderiv ℝ F 0 (y - x)‖ ≤ (a / 4) * ‖y - x‖ := by
    intro x y hx hy
    have hx' : x ∈ Metric.closedBall (0 : ℝ × ℝ) Rx := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx
    have hy' : y ∈ Metric.closedBall (0 : ℝ × ℝ) Rx := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hy
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ)
      (f := F) (f' := fun w => fderiv ℝ F w) (φ := fderiv ℝ F 0) (C := a / 4)
      (s := Metric.closedBall (0 : ℝ × ℝ) Rx) (x := x) (y := y)
      (fun w _ => (hFdiff.differentiableAt.hasFDerivAt).hasFDerivWithinAt)
      (fun w hw => by
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        exact hclose w hw)
      (convex_closedBall _ _) hx' hy'
  -- On the ball, `F` differs from the affine model by at most `(a/4) Rx`.
  have key : ∀ q : ℝ × ℝ, ‖q‖ ≤ Rx → |F q - (a * q.1 + b * q.2)| ≤ (a / 4) * Rx := by
    intro q hq
    have h0 : ‖(0 : ℝ × ℝ)‖ ≤ Rx := by rw [norm_zero]; exact hRx.le
    have h := hmvt (0 : ℝ × ℝ) q h0 hq
    have h1 : ‖F q - (a * q.1 + b * q.2)‖ ≤ (a / 4) * ‖q‖ := by
      simpa [hF0, hder] using h
    rw [← Real.norm_eq_abs]
    calc ‖F q - (a * q.1 + b * q.2)‖ ≤ (a / 4) * ‖q‖ := h1
      _ ≤ (a / 4) * Rx := mul_le_mul_of_nonneg_left hq (by linarith)
  refine ⟨?_, ?_⟩
  · intro y hy
    have hyRx : |y| ≤ Rx := le_trans hy hRyRx
    have hq_pos : ‖((Rx, y) : ℝ × ℝ)‖ ≤ Rx := by
      rw [norm_pair, abs_of_pos hRx]
      exact max_le le_rfl hyRx
    have hq_neg : ‖((-Rx, y) : ℝ × ℝ)‖ ≤ Rx := by
      rw [norm_pair, abs_neg, abs_of_pos hRx]
      exact max_le le_rfl hyRx
    have hby_ub : b * y ≤ |b| * Ry :=
      le_trans (le_abs_self (b * y)) (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hy (abs_nonneg b))
    have hby_lb : -(|b| * Ry) ≤ b * y := by
      have h2 : |b * y| ≤ |b| * Ry := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hy (abs_nonneg b)
      linarith [neg_abs_le (b * y)]
    refine ⟨?_, ?_⟩
    · have h1 : F (-Rx, y) - (a * (-Rx) + b * y) ≤ (a / 4) * Rx :=
        (abs_le.mp (by simpa using key (-Rx, y) hq_neg)).2
      linarith
    · have h1 : -((a / 4) * Rx) ≤ F (Rx, y) - (a * Rx + b * y) :=
        (abs_le.mp (by simpa using key (Rx, y) hq_pos)).1
      linarith
  · intro y hy x₁ hx₁ x₂ hx₂ hlt
    have hyRx : |y| ≤ Rx := le_trans hy hRyRx
    have hx1 : |x₁| ≤ Rx := abs_le.mpr (Set.mem_Icc.mp hx₁)
    have hx2 : |x₂| ≤ Rx := abs_le.mpr (Set.mem_Icc.mp hx₂)
    have hq1 : ‖((x₁, y) : ℝ × ℝ)‖ ≤ Rx := by
      rw [norm_pair]; exact max_le hx1 hyRx
    have hq2 : ‖((x₂, y) : ℝ × ℝ)‖ ≤ Rx := by
      rw [norm_pair]; exact max_le hx2 hyRx
    have hdiff : ((x₂, y) - (x₁, y) : ℝ × ℝ) = (x₂ - x₁, 0) := by ext <;> simp
    have hnorm : ‖((x₂, y) - (x₁, y) : ℝ × ℝ)‖ = x₂ - x₁ := by
      rw [hdiff, norm_pair, abs_zero, max_eq_left (abs_nonneg (x₂ - x₁)),
        abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    have hLval : fderiv ℝ F 0 ((x₂, y) - (x₁, y)) = a * (x₂ - x₁) := by
      rw [hdiff, hder]; simp
    have h := hmvt (x₁, y) (x₂, y) hq1 hq2
    have hh : ‖F (x₂, y) - F (x₁, y) - a * (x₂ - x₁)‖ ≤ (a / 4) * (x₂ - x₁) := by
      rw [hLval, hnorm] at h
      exact h
    have hlow : -((a / 4) * (x₂ - x₁)) ≤ F (x₂, y) - F (x₁, y) - a * (x₂ - x₁) :=
      (abs_le.mp (by rwa [Real.norm_eq_abs] at hh)).1
    have hxd : 0 < x₂ - x₁ := sub_pos.mpr hlt
    have hq : (3 * a / 4) * (x₂ - x₁) ≤ F (x₂, y) - F (x₁, y) := by nlinarith [hlow]
    have hp : 0 < (3 * a / 4) * (x₂ - x₁) := mul_pos (by linarith) hxd
    linarith

end Work.Smooth.BoxGeneric.LocalArc
