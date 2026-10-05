import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- A holomorphic function on the disc `|z| < R` (`R > 1`) which is injective and has nonvanishing
derivative there, traced along the unit circle `t ↦ e^{it}`, is a smooth loop `IsSmoothLoop`.

The four fields of `IsSmoothLoop`:

* *smoothness*: `F` is holomorphic on the open disc, hence analytic and in particular `C^∞` on it;
  the circle `t ↦ e^{it}` stays in the disc (`‖e^{it}‖ = 1 < R`) and the composite is `C^∞`;
* *periodicity*: `t ↦ e^{it}` is `2π`-periodic (`Complex.exp_periodic`);
* *injectivity mod `2π`*: `e^{it}` and `e^{it'}` lie in the disc, so injectivity of `F` there gives
  `e^{it} = e^{it'}`, i.e. `t' = t + 2πm` (`Circle.exp_eq_exp`);
* *immersion*: the chain rule gives `deriv (F ∘ (· ↦ e^{it})) t = deriv F (e^{it}) · (e^{it} · I)`,
  a product of two nonzero factors (`hF'` and `e^{it}, I ≠ 0`). -/
theorem isSmoothLoop_circle_trace (F : ℂ → ℂ) (R : ℝ) (hR : 1 < R)
    (hFd : DifferentiableOn ℂ F (ball 0 R)) (hFi : InjOn F (ball 0 R))
    (hF' : ∀ z ∈ ball 0 R, deriv F z ≠ 0) :
    IsSmoothLoop (fun t : ℝ => F (Complex.exp (t * I))) := by
  -- The circle `t ↦ e^{it}` stays inside the disc `ball 0 R` because `‖e^{it}‖ = 1 < R`.
  have hmem : ∀ t : ℝ, Complex.exp (t * I) ∈ ball (0:ℂ) R := by
    intro t
    rw [mem_ball, dist_zero_right, Complex.norm_exp_ofReal_mul_I]
    exact hR
  -- Derivative of `t ↦ e^{it}`: it is `e^{it} · I`.
  have hexp_hasDerivAt : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Complex.exp (s * I)) (Complex.exp (t * I) * I) t := by
    intro t
    have hinner : HasDerivAt (fun s : ℝ => (s : ℂ) * I) I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
    exact (Complex.hasDerivAt_exp (t * I)).comp t hinner
  have hderiv_exp : ∀ t : ℝ,
      deriv (fun s : ℝ => Complex.exp (s * I)) t = Complex.exp (t * I) * I := by
    intro t
    exact (hexp_hasDerivAt t).deriv
  -- Global smoothness of `t ↦ e^{it}`.
  have hexp_cont : ContDiff ℝ ∞ (fun s : ℝ => Complex.exp (s * I)) :=
    (contDiff_exp (𝕜 := ℝ) (n := ∞)).comp
      ((Complex.ofRealCLM.contDiff).mul (contDiff_const (c := (I:ℂ))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Smoothness of the composite, using that `F` is holomorphic on the open disc.
    rw [contDiff_iff_contDiffAt]
    intro t
    have hFcont : ContDiffOn ℂ ∞ F (ball 0 R) := hFd.contDiffOn isOpen_ball
    have hFat : ContDiffAt ℂ ∞ F (Complex.exp (t * I)) :=
      hFcont.contDiffAt (isOpen_ball.mem_nhds (hmem t))
    have hFar : ContDiffAt ℝ ∞ F (Complex.exp (t * I)) := hFat.restrict_scalars ℝ
    exact hFar.comp t hexp_cont.contDiffAt
  · -- `2π`-periodicity.
    intro t
    change F (Complex.exp ((↑(t + 2 * π) : ℂ) * I)) = F (Complex.exp ((↑t : ℂ) * I))
    have harg : (↑(t + 2 * π) : ℂ) * I = (↑t : ℂ) * I + 2 * ↑π * I := by push_cast; ring
    rw [harg, Complex.exp_periodic (↑t * I)]
  · -- Injectivity modulo `2π`.
    intro t t' h
    have heq : Complex.exp (t * I) = Complex.exp (t' * I) := hFi (hmem t) (hmem t') h
    have hc : Circle.exp t = Circle.exp t' := by
      apply Subtype.ext
      rw [Circle.coe_exp, Circle.coe_exp]
      exact heq
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hc
    refine ⟨-m, ?_⟩
    rw [hm]; push_cast; ring
  · -- Immersion: chain rule, both factors nonzero.
    intro t
    have hFd_at : DifferentiableAt ℂ F (Complex.exp (t * I)) :=
      hFd.differentiableAt (isOpen_ball.mem_nhds (hmem t))
    have hhdiff : DifferentiableAt ℝ (fun s : ℝ => Complex.exp (s * I)) t :=
      (hexp_hasDerivAt t).differentiableAt
    have hmain : deriv (fun s : ℝ => F (Complex.exp (s * I))) t
        = deriv F (Complex.exp (t * I)) * deriv (fun s : ℝ => Complex.exp (s * I)) t := by
      simpa only [Function.comp_def] using deriv_comp t hFd_at hhdiff
    rw [hmain, hderiv_exp t]
    exact mul_ne_zero (hF' _ (hmem t)) (mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero)

end Work.RPB1a
