import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Calculus

open Filter Set
open scoped Topology

/-- At a twice continuously differentiable local minimum, the second derivative (in the sense of
the iterated `deriv`) is nonnegative.

Proof: by Fermat's theorem `deriv f x = 0`. If `deriv (deriv f) x < 0`, then the sign of
`deriv f` matches `x - ·` in a neighbourhood of `x`, so `deriv f` is strictly negative on a
right-neighbourhood of `x`. Using the continuity of `f` there, the mean value theorem makes `f`
strictly decreasing on that interval, producing a point `y > x` with `f y < f x`, a contradiction
with `IsLocalMin f x`. -/
theorem localMin_second_deriv_nonneg (f : ℝ → ℝ) (x : ℝ)
    (hmin : IsLocalMin f x) (hd : ContDiffAt ℝ 2 f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra h
  push Not at h
  have hx0 : deriv f x = 0 := hmin.deriv_eq_zero
  have hsign : ∀ᶠ y in 𝓝 x, SignType.sign (deriv f y) = SignType.sign (x - y) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg h hx0
  have hcd : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y := hd.eventually (by norm_num)
  let W : Set ℝ := {y | ContDiffAt ℝ 2 f y ∧
    SignType.sign (deriv f y) = SignType.sign (x - y) ∧ f x ≤ f y}
  have hW : W ∈ 𝓝 x := by
    filter_upwards [hcd, hsign, hmin] with y h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hW
  set δ := ε / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by rw [hδdef]; linarith
  have hxδ : x < x + δ := by linarith
  have hball : Icc x (x + δ) ⊆ Metric.ball x ε := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq]
    have : |y - x| ≤ δ := by
      rw [abs_of_nonneg (by linarith [hy.1])]
      linarith [hy.2]
    linarith
  have hcontW : ContinuousOn f W := fun y hy => hy.1.continuousAt.continuousWithinAt
  have hcont : ContinuousOn f (Icc x (x + δ)) := hcontW.mono (fun y hy => hsub (hball hy))
  have hderiv : ∀ y ∈ interior (Icc x (x + δ)), deriv f y < 0 := by
    rw [interior_Icc]
    intro y hy
    have hyW : y ∈ W := hsub (hball ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
    rw [← sign_eq_neg_one_iff, hyW.2.1, sign_eq_neg_one_iff]
    linarith [hy.1]
  have hanti : StrictAntiOn f (Icc x (x + δ)) :=
    strictAntiOn_of_deriv_neg (convex_Icc x (x + δ)) hcont hderiv
  have hlt : f (x + δ) < f x :=
    hanti ⟨le_refl x, le_of_lt hxδ⟩ ⟨le_of_lt hxδ, le_refl _⟩ hxδ
  have hle : f x ≤ f (x + δ) := by
    have hb : x + δ ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, show x + δ - x = δ by ring, abs_of_pos hδpos]
      exact hδlt
    exact (hsub hb).2.2
  linarith

end Commons.Analysis.Calculus