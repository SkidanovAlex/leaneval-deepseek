import Mathlib
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig.LocalInverse

open Set Metric Filter
open scoped Topology

/-- If `f : ℂ → ℂ` is differentiable and injective on a ball `Metric.ball c r`, then its
derivative does not vanish at any point of this ball. -/
theorem deriv_ne_zero_of_injOn_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {r : ℝ}
    (hinj : Set.InjOn f (Metric.ball c r)) {z : ℂ} (hz : z ∈ Metric.ball c r) :
    deriv f z ≠ 0 := by
  have hzr : dist z c < r := Metric.mem_ball.mp hz
  have hr : 0 < r - dist z c := by linarith
  refine Work.ELRig.deriv_ne_zero_of_injOn hf.differentiableOn Metric.isOpen_ball ?_
    (Metric.mem_ball_self hr)
  intro a ha b hb hab
  have ha' : a ∈ Metric.ball c r := by
    rw [Metric.mem_ball] at ha ⊢
    calc dist a c ≤ dist a z + dist z c := dist_triangle a z c
      _ < (r - dist z c) + dist z c := by linarith
      _ = r := by ring
  have hb' : b ∈ Metric.ball c r := by
    rw [Metric.mem_ball] at hb ⊢
    calc dist b c ≤ dist b z + dist z c := dist_triangle b z c
      _ < (r - dist z c) + dist z c := by linarith
      _ = r := by ring
  exact hinj ha' hb' hab

/-- **The holomorphic inverse function theorem** (local form).

Let `Ψ : ℂ → ℂ` be differentiable everywhere and injective on some ball around `x`. Then `Ψ`
admits an analytic local inverse `σ` near `Ψ x`, and `σ` is differentiable there with non-zero
derivative.

The point is that local injectivity forces `deriv Ψ x ≠ 0` (a holomorphic function with a vanishing
derivative is `n`-to-one near that point, see `Work.ELRig.deriv_ne_zero_of_injOn`), and then
Mathlib's inverse function theorem (`HasStrictDerivAt.localInverse`) produces a local inverse that
is analytic (`AnalyticAt.analyticAt_localInverse`, and analyticity is propagated to the whole ball
of convergence with `analyticAt_comp_iff_of_deriv_ne_zero`). -/
theorem exists_analytic_localInverse {Ψ : ℂ → ℂ} (hΨ : Differentiable ℂ Ψ) {x : ℂ}
    (hinj : ∃ δ > 0, Set.InjOn Ψ (Metric.ball x δ)) :
    ∃ δ₁ > 0, ∃ δ₂ > 0, ∃ σ : ℂ → ℂ,
      AnalyticOnNhd ℂ σ (Metric.ball (Ψ x) δ₂) ∧
      (∀ z ∈ Metric.ball (Ψ x) δ₂, Ψ (σ z) = z) ∧
      (∀ w ∈ Metric.ball x δ₁, σ (Ψ w) = w) ∧
      deriv σ (Ψ x) ≠ 0 := by
  obtain ⟨δ, hδpos, hinjδ⟩ := hinj
  -- local injectivity forces a non-vanishing derivative at `x`
  have hderiv : deriv Ψ x ≠ 0 :=
    deriv_ne_zero_of_injOn_ball hΨ hinjδ (Metric.mem_ball_self hδpos)
  have hstrict : HasStrictDerivAt Ψ (deriv Ψ x) x := (hΨ.analyticAt x).hasStrictDerivAt
  -- the local inverse produced by the (strict) inverse function theorem
  let σ : ℂ → ℂ := HasStrictDerivAt.localInverse Ψ (deriv Ψ x) x hstrict hderiv
  have hσ_left : ∀ᶠ u in 𝓝 x, σ (Ψ u) = u := hstrict.eventually_left_inverse hderiv
  have hσ_right : ∀ᶠ y in 𝓝 (Ψ x), Ψ (σ y) = y := hstrict.eventually_right_inverse hderiv
  have hσ_strict : HasStrictDerivAt σ (deriv Ψ x)⁻¹ (Ψ x) := hstrict.to_localInverse hderiv
  have hσ_x : σ (Ψ x) = x := hσ_left.self_of_nhds
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp hσ_left
  -- `σ` maps a small ball around `Ψ x` into the ball around `x` where both the injectivity
  -- hypothesis and the left inverse property are available
  have hεpos : 0 < min δ ε₁ := lt_min hδpos hε₁pos
  have hσ_mem : ∀ᶠ y in 𝓝 (Ψ x), σ y ∈ Metric.ball x (min δ ε₁) := by
    have := (hσ_strict.hasDerivAt.continuousAt).preimage_mem_nhds
      (by rw [hσ_x]; exact Metric.ball_mem_nhds x hεpos)
    exact this
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhds_iff.mp (hσ_mem.and hσ_right)
  refine ⟨ε₁, hε₁pos, δ₂, hδ₂pos, σ, ?_, ?_, ?_, ?_⟩
  · -- analyticity of `σ` on the ball: use that `σ ∘ Ψ = id` near `σ w` and the inverse
    -- function theorem in the form `analyticAt_comp_iff_of_deriv_ne_zero`
    intro w hw
    have hwσ : σ w ∈ Metric.ball x (min δ ε₁) := (hδ₂ hw).1
    have hwΨ : Ψ (σ w) = w := (hδ₂ hw).2
    have hzδ : σ w ∈ Metric.ball x δ := Metric.ball_subset_ball (min_le_left _ _) hwσ
    have hzε : σ w ∈ Metric.ball x ε₁ := Metric.ball_subset_ball (min_le_right _ _) hwσ
    have hzd : deriv Ψ (σ w) ≠ 0 := deriv_ne_zero_of_injOn_ball hΨ hinjδ hzδ
    have hz_an : AnalyticAt ℂ Ψ (σ w) := hΨ.analyticAt (σ w)
    have hcomp : AnalyticAt ℂ (σ ∘ Ψ) (σ w) := by
      have heq : id =ᶠ[𝓝 (σ w)] σ ∘ Ψ := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzε] with u hu
        show id u = (σ ∘ Ψ) u
        simp only [id_eq, Function.comp_apply]
        exact (hε₁ hu).symm
      exact analyticAt_id.congr heq
    have hfin : AnalyticAt ℂ σ (Ψ (σ w)) :=
      (analyticAt_comp_iff_of_deriv_ne_zero hz_an hzd).mp hcomp
    rwa [hwΨ] at hfin
  · intro z hz
    exact (hδ₂ hz).2
  · intro w hw
    exact hε₁ hw
  · rw [hσ_strict.hasDerivAt.deriv]
    exact inv_ne_zero hderiv

end Work.ELRig.LocalInverse
