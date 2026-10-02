import Mathlib
import Submission.Work.ELRig.LocalInverse.exists_analytic_localInverse
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Metric Filter
open scoped Topology

/-- **The analytic inverse function theorem**, local form for functions that are only analytic on
an open set `U` (and injective there).

If `f` is analytic on the open set `U` and injective on `U`, then at each `x₀ ∈ U` there is an
analytic local inverse `σ` of `f` on a ball around `f x₀`: `σ` is analytic on that ball, it is a
right inverse of `f` there, it maps that ball into `U`, and its derivative at `f x₀` is non-zero.

The proof is the one of `Work.ELRig.LocalInverse.exists_analytic_localInverse`, with the global
differentiability hypothesis replaced by analyticity on `U`; the non-vanishing of `deriv f x₀`
comes from `Work.ELRig.deriv_ne_zero_of_injOn`. -/
theorem exists_analytic_localInverse_of_injOn {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hinj : Set.InjOn f U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ δ > 0, ∃ σ : ℂ → ℂ,
      AnalyticOnNhd ℂ σ (Metric.ball (f x₀) δ) ∧
      (∀ z ∈ Metric.ball (f x₀) δ, f (σ z) = z) ∧
      (∀ z ∈ Metric.ball (f x₀) δ, σ z ∈ U) ∧
      deriv σ (f x₀) ≠ 0 := by
  have hfx₀ : AnalyticAt ℂ f x₀ := hf x₀ hx₀
  -- local injectivity forces a non-vanishing derivative at `x₀`
  have hderiv : deriv f x₀ ≠ 0 :=
    Work.ELRig.deriv_ne_zero_of_injOn hf.differentiableOn hU hinj hx₀
  have hstrict : HasStrictDerivAt f (deriv f x₀) x₀ := hfx₀.hasStrictDerivAt
  -- the local inverse produced by the (strict) inverse function theorem
  let σ : ℂ → ℂ := HasStrictDerivAt.localInverse f (deriv f x₀) x₀ hstrict hderiv
  have hσ_left : ∀ᶠ u in 𝓝 x₀, σ (f u) = u := hstrict.eventually_left_inverse hderiv
  have hσ_right : ∀ᶠ y in 𝓝 (f x₀), f (σ y) = y := hstrict.eventually_right_inverse hderiv
  have hσ_strict : HasStrictDerivAt σ (deriv f x₀)⁻¹ (f x₀) := hstrict.to_localInverse hderiv
  have hσ_x : σ (f x₀) = x₀ := hσ_left.self_of_nhds
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp hσ_left
  -- a ball around `x₀` contained in `U`
  obtain ⟨ρ, hρpos, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  -- `σ` maps a small ball around `f x₀` into `ball x₀ (min ρ ε₁)`
  have hεpos : 0 < min ρ ε₁ := lt_min hρpos hε₁pos
  have hσ_mem : ∀ᶠ y in 𝓝 (f x₀), σ y ∈ Metric.ball x₀ (min ρ ε₁) :=
    (hσ_strict.hasDerivAt.continuousAt).preimage_mem_nhds
      (by rw [hσ_x]; exact Metric.ball_mem_nhds x₀ hεpos)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (hσ_mem.and hσ_right)
  refine ⟨δ, hδpos, σ, ?_, ?_, ?_, ?_⟩
  · -- analyticity of `σ` on the ball: use that `σ ∘ f = id` near `σ w` and the inverse
    -- function theorem in the form `analyticAt_comp_iff_of_deriv_ne_zero`
    intro w hw
    have hwσ : σ w ∈ Metric.ball x₀ (min ρ ε₁) := (hδ hw).1
    have hwΨ : f (σ w) = w := (hδ hw).2
    have hσwU : σ w ∈ U := hρU (Metric.ball_subset_ball (min_le_left _ _) hwσ)
    have hzε : σ w ∈ Metric.ball x₀ ε₁ := Metric.ball_subset_ball (min_le_right _ _) hwσ
    have hzd : deriv f (σ w) ≠ 0 :=
      Work.ELRig.deriv_ne_zero_of_injOn hf.differentiableOn hU hinj hσwU
    have hz_an : AnalyticAt ℂ f (σ w) := hf (σ w) hσwU
    have hcomp : AnalyticAt ℂ (σ ∘ f) (σ w) := by
      have heq : id =ᶠ[𝓝 (σ w)] σ ∘ f := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzε] with u hu
        show id u = (σ ∘ f) u
        simp only [id_eq, Function.comp_apply]
        exact (hε₁ hu).symm
      exact analyticAt_id.congr heq
    have hfin : AnalyticAt ℂ σ (f (σ w)) :=
      (analyticAt_comp_iff_of_deriv_ne_zero hz_an hzd).mp hcomp
    rwa [hwΨ] at hfin
  · intro z hz
    exact (hδ hz).2
  · intro z hz
    exact hρU (Metric.ball_subset_ball (min_le_left _ _) (hδ hz).1)
  · rw [hσ_strict.hasDerivAt.deriv]
    exact inv_ne_zero hderiv

/-- **The set-theoretic inverse of an injective analytic function is analytic on its image.**

`Function.invFunOn f U` is the chosen inverse of `f` on `f '' U`; there it is locally the inverse
produced by the analytic inverse function theorem.  Route: at `y₀ = f x₀` (`x₀ ∈ U`) obtain an
analytic local inverse `σ` of `f` at `x₀` (a version of
`Work.ELRig.LocalInverse.exists_analytic_localInverse` with `AnalyticOnNhd ℂ f U`, `IsOpen U`,
`InjOn f U`, `x₀ ∈ U` in place of the global `Differentiable ℂ f`; copy that file's proof, using
`Work.ELRig.deriv_ne_zero_of_injOn` for `deriv f x₀ ≠ 0`); then for `y` near `y₀`,
`σ y ∈ U` (continuity, `U` open) and `f (σ y) = y`, while *every* `w ∈ U` with `f w = y` equals
`σ y` because `f` is injective on `U` and both `w`, `σ y` lie in `U`.  Hence `invFunOn f U = σ`
near `y₀` (`Function.invFunOn_eq`) and `invFunOn f U` is analytic at `y₀`. -/
theorem analyticOnNhd_invFunOn {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hinj : Set.InjOn f U) :
    AnalyticOnNhd ℂ (Function.invFunOn f U) (f '' U) := by
  intro y hy
  obtain ⟨x₀, hx₀U, rfl⟩ := hy
  obtain ⟨δ, hδpos, σ, hσ_an, hσ_right, hσ_mem, _⟩ :=
    exists_analytic_localInverse_of_injOn hU hf hinj hx₀U
  -- `invFunOn f U` agrees with `σ` on a ball around `f x₀`
  have heq : Function.invFunOn f U =ᶠ[𝓝 (f x₀)] σ := by
    filter_upwards [Metric.ball_mem_nhds (f x₀) hδpos] with z hz
    have hzσU : σ z ∈ U := hσ_mem z hz
    have hzσf : f (σ z) = z := hσ_right z hz
    have hmem : ∃ a ∈ U, f a = z := ⟨σ z, hzσU, hzσf⟩
    have h1 : Function.invFunOn f U z ∈ U := Function.invFunOn_mem hmem
    have h2 : f (Function.invFunOn f U z) = z := Function.invFunOn_eq hmem
    exact hinj h1 hzσU (h2.trans hzσf.symm)
  exact (hσ_an (f x₀) (Metric.mem_ball_self hδpos)).congr heq.symm

end Work.ELRig
