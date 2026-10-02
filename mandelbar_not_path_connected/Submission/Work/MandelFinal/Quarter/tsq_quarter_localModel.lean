import Mathlib
import Submission.Work.LANDCL.Quarter.isParabolic_quarter_half
import Submission.Work.LANDCL.Deriv.tsq_deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology

namespace Work.MandelFinal.Quarter

/-- **The local model of the cusp `1/2` for the holomorphic second return map `Tsq (1/4)`.**

`Tsq (1/4) = (T_{1/4})^[2]` is a holomorphic polynomial with `Tsq (1/4) (1/2) = 1/2` and
`deriv (Tsq (1/4)) (1/2) = 1 ≠ 0`. Hence (strict inverse function theorem,
`AnalyticAt.hasStrictDerivAt` + `HasStrictDerivAt.localInverse`, exactly as in
`Submission/Work/LandLeaves/exists_local_repelling_branch.lean`) `Tsq (1/4)` is injective on a
ball around `1/2` and has a local inverse branch `g` inverting it on a pair of concentric balls.
No contraction property is recorded: at a *parabolic* point the multiplier is `1`, so no
contraction is available; the left-inverse property on the two balls is the only thing the
landing-theory arguments use. -/
theorem tsq_quarter_localModel :
    Work.Landing.Tsq (1 / 4 : ℂ) (1 / 2) = 1 / 2 ∧
    deriv (Work.Landing.Tsq (1 / 4 : ℂ)) (1 / 2) = 1 ∧
    (∃ r : ℝ, 0 < r ∧ Set.InjOn (Work.Landing.Tsq (1 / 4 : ℂ)) (Metric.ball (1 / 2) r)) ∧
    (∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - (1 / 2 : ℂ)‖ ≤ r → ‖Work.Landing.Tsq (1 / 4 : ℂ) z - (1 / 2 : ℂ)‖ ≤ r' →
      g (Work.Landing.Tsq (1 / 4 : ℂ) z) = z) := by
  -- `1/2` is fixed by `Tsq (1/4)` (the cusp of the period-`1` hyperbolic component).
  have hfix : Work.Landing.Tsq (1 / 4 : ℂ) (1 / 2) = 1 / 2 := by
    simp only [Work.Landing.Tsq_apply]
    norm_num
  -- the multiplier at `1/2` is `1` (parabolic fixed point).
  have hderiv : deriv (Work.Landing.Tsq (1 / 4 : ℂ)) (1 / 2) = 1 := by
    rw [Work.LANDCL.Deriv.tsq_deriv]
    norm_num
  -- `Tsq (1/4)` is a polynomial, hence entire, hence analytic; its strict derivative at `1/2`
  -- is the multiplier `1`.
  have hf_diff : Differentiable ℂ (Work.Landing.Tsq (1 / 4 : ℂ)) := by
    show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star (1 / 4)) ^ 2 + 1 / 4)
    fun_prop
  have hstrict : HasStrictDerivAt (Work.Landing.Tsq (1 / 4 : ℂ)) 1 (1 / 2) := by
    have h := (hf_diff.analyticAt (1 / 2)).hasStrictDerivAt
    rwa [hderiv] at h
  -- the inverse function theorem gives the local inverse branch `g`.
  have hne : (1 : ℂ) ≠ 0 := one_ne_zero
  let g : ℂ → ℂ :=
    HasStrictDerivAt.localInverse (Work.Landing.Tsq (1 / 4 : ℂ)) 1 (1 / 2) hstrict hne
  have hg_left : ∀ᶠ u in 𝓝 (1 / 2 : ℂ), g (Work.Landing.Tsq (1 / 4 : ℂ) u) = u := by
    have h := HasStrictDerivAt.eventually_left_inverse (f := Work.Landing.Tsq (1 / 4 : ℂ))
      (f' := (1 : ℂ)) (a := (1 / 2 : ℂ)) hstrict hne
    simpa [g] using h
  -- a radius on which `g` is a left inverse (equivalently, on which `Tsq (1/4)` is injective).
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hg_left
  have hδ' : ∀ u : ℂ, dist u (1 / 2 : ℂ) < δ → g (Work.Landing.Tsq (1 / 4 : ℂ) u) = u :=
    fun u hu => hδ (by rwa [Metric.mem_ball])
  refine ⟨hfix, hderiv, ?_, ?_⟩
  · -- injectivity on the ball of radius `δ / 2`: `g` is a left inverse there.
    refine ⟨δ / 2, by positivity, ?_⟩
    intro a ha b hb hab
    have ha' : dist a (1 / 2 : ℂ) < δ := by
      have := ha; rw [Metric.mem_ball] at this; linarith
    have hb' : dist b (1 / 2 : ℂ) < δ := by
      have := hb; rw [Metric.mem_ball] at this; linarith
    have h1 := hδ' a ha'
    have h2 := hδ' b hb'
    rw [hab] at h1
    exact h1.symm.trans h2
  · -- the left-inverse property on the pair of concentric balls of radius `δ / 2`.
    refine ⟨δ / 2, δ / 2, g, by positivity, by positivity, ?_⟩
    intro z hz _
    apply hδ'
    rw [dist_eq_norm]
    linarith

end Work.MandelFinal.Quarter
