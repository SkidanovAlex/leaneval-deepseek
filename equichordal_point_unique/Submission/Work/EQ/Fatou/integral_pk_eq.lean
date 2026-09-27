import Mathlib
import Submission.Work.EQ.FatouDefs
import Submission.Work.EQ.Fatou.pk_eq_poissonKernel

/-! The angle Poisson kernel `pk r ψ` has total mass `2π` on a full period.

This is the classical fact that the Poisson kernel on the unit circle is (the density of) a
probability measure: `circleAverage (poissonKernel 0 r) 0 1 = 1` for `r` in the unit disc.  We
deduce it from Mathlib's Poisson integral formula applied to the constant function `1`, then
use `2π`-periodicity of the kernel on the circle to move the interval `[0, 2π]` to `[-π, π]`.
-/

namespace Work.EQ.Fatou

open Complex MeasureTheory Metric Real Set

/-- The angle Poisson kernel equals the (disc) Poisson kernel `poissonKernel` of the unit circle
at the point `r ∈ (-1, 1)`, evaluated at the point `e^{iψ}`. -/
lemma pk_eq_poissonKernel_circle (r ψ : ℝ) (hr1 : r < 1) :
    Work.EQ.pk r ψ = poissonKernel 0 (r : ℂ) (circleMap 0 1 ψ) := by
  have h := pk_eq_poissonKernel r 0 ψ hr1
  simp only [zero_sub] at h
  rw [Work.EQ.pk, Real.cos_neg] at h
  have hcircle : circleMap 0 1 ψ = Complex.exp ((ψ : ℂ) * Complex.I) := by
    simp [circleMap]
  rw [hcircle]
  simpa [Work.EQ.pk] using h

/-- **The Poisson kernel integrates to one over the unit circle.** -/
theorem circleAverage_poissonKernel_one (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun z : ℂ => ((poissonKernel 0 (r : ℂ) z : ℝ) : ℂ)) 0 1 = 1 := by
  have h := DiffContOnCl.circleAverage_poissonKernel_smul
    (f := (fun _ : ℂ => (1 : ℂ))) (c := (0 : ℂ)) (R := (1 : ℝ)) (w := (r : ℂ))
    (by exact differentiable_const (1 : ℂ) |>.diffContOnCl)
    (by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr]; exact hr1)
  have hfun : (fun z : ℂ => ((poissonKernel 0 (r : ℂ) z : ℝ) : ℂ))
      = poissonKernel 0 (r : ℂ) • (fun _ => (1 : ℂ)) := by
    ext z; simp [Complex.real_smul]
  rw [hfun, h]

/-- The real integral of the Poisson kernel over one full period is `2π`. -/
theorem integral_poissonKernel_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) = 2 * π := by
  have hpois := circleAverage_poissonKernel_one r hr hr1
  rw [Real.circleAverage_def] at hpois
  have hint : (∫ θ in (0 : ℝ)..2 * π, ((poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) : ℝ) : ℂ))
      = ((∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) : ℝ) : ℂ) :=
    RCLike.intervalIntegral_ofReal
  rw [hint] at hpois
  rw [Complex.real_smul, ← Complex.ofReal_mul] at hpois
  have h2 : (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)) = 1 := by
    rw [← Complex.ofReal_one] at hpois
    exact Complex.ofReal_inj.mp hpois
  have hne : (2 * π : ℝ) ≠ 0 := by positivity
  rw [inv_mul_eq_iff_eq_mul₀ hne, mul_one] at h2
  exact h2

theorem integral_pk_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∫ ψ in (-Real.pi)..Real.pi, Work.EQ.pk r ψ = 2 * Real.pi := by
  -- Move the interval `[0, 2π]` to `[-π, π]` using `2π`-periodicity on the circle.
  have hJ := integral_poissonKernel_eq r hr hr1
  have hper : ∫ ψ in (-π)..π, poissonKernel 0 (r : ℂ) (circleMap 0 1 ψ) = 2 * π := by
    have hf : Function.Periodic (fun θ : ℝ => poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)) (2 * π) :=
      fun θ => by
        show poissonKernel 0 (r : ℂ) (circleMap 0 1 (θ + 2 * π))
          = poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)
        rw [periodic_circleMap]
    have hpi : -π + 2 * π = π := by ring
    have h := hf.intervalIntegral_add_eq (0 : ℝ) (-π)
    simp only [zero_add] at h
    rw [hpi] at h
    rw [← h]
    exact hJ
  have hcongr : (∫ ψ in (-π)..π, Work.EQ.pk r ψ)
      = ∫ ψ in (-π)..π, poissonKernel 0 (r : ℂ) (circleMap 0 1 ψ) := by
    apply intervalIntegral.integral_congr
    intro ψ _
    exact pk_eq_poissonKernel_circle r ψ hr1
  rw [hcongr, hper]

end Work.EQ.Fatou
