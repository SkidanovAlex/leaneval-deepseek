import Mathlib
import Submission.Work.Kernels.Classical

/-!
# Lipschitz continuity of a holomorphic function of the `q`-parameter

A function `f` on the upper half plane which is invariant under `τ ↦ τ + 1`, holomorphic, and
bounded at the cusp `i∞` is a holomorphic function of `q = e^{2πiτ}` on the unit disc: this is
`UpperHalfPlane.cuspFunction 1 f`, which is differentiable on `ball 0 1` by
`UpperHalfPlane.differentiableOn_cuspFunction_ball`.

A holomorphic function has a holomorphic derivative, so `deriv (cuspFunction 1 f)` is bounded on
the compact disc `closedBall 0 (1/2)`; the mean value inequality
(`Convex.norm_image_sub_le_of_norm_deriv_le`) then gives a Lipschitz bound there.  Transporting
back along `q` yields the statement: away from the cusp, `f` is Lipschitz in `q`.
-/

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Manifold

/-- **`f` is Lipschitz in `q` near the cusp.**  If `f` is `1`-periodic, holomorphic on `ℍ` and
bounded at `i∞`, then there is a constant `C > 0` with
`‖f τ - f z‖ ≤ C * ‖q τ - q z‖` for all `τ, z` with `‖q‖ ≤ 1/2`. -/
theorem cuspFunction_diff_lipschitz {f : UpperHalfPlane → ℂ}
    (hper : ∀ τ : UpperHalfPlane, f ((1 : ℝ) +ᵥ τ) = f τ)
    (hhol : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im})
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ z : UpperHalfPlane,
      ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 2 → ‖Work.Kernels.qParamFun z‖ ≤ 1 / 2 →
      ‖f τ - f z‖ ≤ C * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖ := by
  -- `hper` as a strict period of the lift `f ∘ ofComplex` to `ℂ`
  have hper' : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1 := by
    intro z
    rcases lt_or_ge (0 : ℝ) z.im with hz | hz
    · have h1 : 0 < (z + 1).im := by simpa using hz
      show f (UpperHalfPlane.ofComplex (z + 1)) = f (UpperHalfPlane.ofComplex z)
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos h1, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      have hvv : (⟨z + 1, h1⟩ : UpperHalfPlane) = (1 : ℝ) +ᵥ (⟨z, hz⟩ : UpperHalfPlane) := by
        ext
        simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_one]
        ring
      rw [hvv]
      exact hper ⟨z, hz⟩
    · have h1 : (z + 1).im ≤ 0 := by simpa using hz
      show f (UpperHalfPlane.ofComplex (z + 1)) = f (UpperHalfPlane.ofComplex z)
      rw [UpperHalfPlane.ofComplex_apply_of_im_nonpos h1,
        UpperHalfPlane.ofComplex_apply_of_im_nonpos hz]
  have hfhol : MDiff f := UpperHalfPlane.mdifferentiable_iff.mpr hhol
  -- the local parameter at the cusp
  have hgdiff : DifferentiableOn ℂ (UpperHalfPlane.cuspFunction 1 f) (Metric.ball 0 1) :=
    UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos hper' hfhol hbdd
  have hgAna : AnalyticOnNhd ℂ (UpperHalfPlane.cuspFunction 1 f) (Metric.ball 0 1) :=
    hgdiff.analyticOnNhd Metric.isOpen_ball
  -- its derivative is continuous, hence bounded on the compact disc of radius `1/2`
  have hderivCont : ContinuousOn (deriv (UpperHalfPlane.cuspFunction 1 f))
      (Metric.closedBall 0 (1 / 2)) :=
    ((hgAna.deriv_of_isOpen Metric.isOpen_ball).continuousOn).mono
      (Metric.closedBall_subset_ball (by norm_num))
  obtain ⟨C0, hC0⟩ :=
    isCompact_closedBall (0 : ℂ) (1 / 2) |>.exists_bound_of_continuousOn hderivCont
  refine ⟨max C0 1, lt_max_of_lt_right zero_lt_one, ?_⟩
  intro τ z hτ hz
  have hqτ : Work.Kernels.qParamFun τ = Function.Periodic.qParam 1 (τ : ℂ) := by
    simp [Work.Kernels.qParamFun, Function.Periodic.qParam]
  have hqz : Work.Kernels.qParamFun z = Function.Periodic.qParam 1 (z : ℂ) := by
    simp [Work.Kernels.qParamFun, Function.Periodic.qParam]
  have hfτ : f τ = UpperHalfPlane.cuspFunction 1 f (Work.Kernels.qParamFun τ) := by
    rw [hqτ]
    exact (UpperHalfPlane.eq_cuspFunction τ one_ne_zero hper').symm
  have hfz : f z = UpperHalfPlane.cuspFunction 1 f (Work.Kernels.qParamFun z) := by
    rw [hqz]
    exact (UpperHalfPlane.eq_cuspFunction z one_ne_zero hper').symm
  have hmem : ∀ u ∈ Metric.closedBall (0 : ℂ) (1 / 2), u ∈ Metric.ball (0 : ℂ) 1 := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hdiff : ∀ u ∈ Metric.closedBall (0 : ℂ) (1 / 2),
      DifferentiableAt ℂ (UpperHalfPlane.cuspFunction 1 f) u :=
    fun u hu => hgdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (hmem u hu))
  have hx : Work.Kernels.qParamFun τ ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hτ
  have hy : Work.Kernels.qParamFun z ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hz
  have hmain : ‖UpperHalfPlane.cuspFunction 1 f (Work.Kernels.qParamFun z)
        - UpperHalfPlane.cuspFunction 1 f (Work.Kernels.qParamFun τ)‖
      ≤ C0 * ‖Work.Kernels.qParamFun z - Work.Kernels.qParamFun τ‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hC0 (convex_closedBall (0 : ℂ) (1 / 2)) hx hy
  calc ‖f τ - f z‖
      = ‖UpperHalfPlane.cuspFunction 1 f (Work.Kernels.qParamFun τ)
          - UpperHalfPlane.cuspFunction 1 f (Work.Kernels.qParamFun z)‖ := by rw [hfτ, hfz]
    _ = ‖UpperHalfPlane.cuspFunction 1 f (Work.Kernels.qParamFun z)
          - UpperHalfPlane.cuspFunction 1 f (Work.Kernels.qParamFun τ)‖ := norm_sub_rev _ _
    _ ≤ C0 * ‖Work.Kernels.qParamFun z - Work.Kernels.qParamFun τ‖ := hmain
    _ = C0 * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖ := by rw [norm_sub_rev]
    _ ≤ max C0 1 * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

end Work.Asymptotics
