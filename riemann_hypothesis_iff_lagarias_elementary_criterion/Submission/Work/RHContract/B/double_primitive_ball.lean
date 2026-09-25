import Mathlib

namespace Work.RHContract.B

open Complex Metric Filter

/-- On a ball (which is convex, hence simply connected), every analytic function has an
analytic double primitive: given `g` analytic on `ball c r`, a point `a ∈ ball c r`, and
values `v v' : ℂ`, there is `P` analytic on `ball c r` with `P a = v`, `P' a = v'` and
`P'' = g` on `ball c r`.

The construction is a double antiderivative: Morera's theorem for disks
(`DifferentiableOn.isExactOn_ball`) first produces `G` with `G' = g` on the ball, then a
second application produces `Q` with `Q' = G` on the ball, so `Q'' = g`; finally `Q` is
adjusted by an affine function so as to realise the prescribed value and first derivative
at `a`. -/
theorem double_primitive_ball (g : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hg : AnalyticOn ℂ g (Metric.ball c r))
    (a : ℂ) (ha : a ∈ Metric.ball c r) (v v' : ℂ) :
    ∃ P : ℂ → ℂ, AnalyticOn ℂ P (Metric.ball c r) ∧ P a = v ∧ deriv P a = v' ∧
      (∀ z ∈ Metric.ball c r, deriv (deriv P) z = g z) := by
  -- First antiderivative `G` of `g` on the ball.
  obtain ⟨G, hG⟩ := hg.differentiableOn.isExactOn_ball
  -- `G` is differentiable, hence analytic, on the ball.
  have hGdiff : DifferentiableOn ℂ G (Metric.ball c r) :=
    fun z hz => (hG z hz).differentiableAt.differentiableWithinAt
  -- Second antiderivative `Q` of `G`: then `deriv (deriv Q) = g` on the ball.
  obtain ⟨Q, hQ⟩ := hGdiff.isExactOn_ball
  -- `C` corrects the first derivative at `a` without touching the second derivative.
  set C : ℂ := v' - G a with hC
  set P : ℂ → ℂ := fun z => Q z + C * (z - a) + (v - Q a) with hPdef
  have hP : ∀ z ∈ Metric.ball c r, HasDerivAt P (G z + C) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => C * (z - a)) C z := by
      simpa using ((hasDerivAt_id z).sub_const a).const_mul C
    have h2 : HasDerivAt (fun z => Q z + C * (z - a)) (G z + C) z := (hQ z hz).add h1
    have h3 : HasDerivAt (fun z => Q z + C * (z - a) + (v - Q a)) (G z + C) z :=
      h2.add_const (v - Q a)
    rwa [hPdef]
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · -- `P` is analytic on the ball, being differentiable there.
    rw [Complex.analyticOn_iff_differentiableOn isOpen_ball]
    intro z hz
    exact (hP z hz).differentiableAt.differentiableWithinAt
  · -- prescribed value: `P a = v`
    rw [hPdef]
    simp only
    ring
  · -- prescribed first derivative: `deriv P a = v'`
    have h := (hP a ha).deriv
    rw [h, hC]
    ring
  · -- second derivative: `deriv (deriv P) = g` on the ball
    intro z hz
    have heq : deriv P =ᶠ[nhds z] (fun w => G w + C) := by
      filter_upwards [IsOpen.mem_nhds isOpen_ball hz] with w hw
      exact (hP w hw).deriv
    rw [heq.deriv_eq]
    exact ((hG z hz).add_const C).deriv

end Work.RHContract.B
