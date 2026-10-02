import Mathlib
import Submission.Work.ELRig.LocalInverse.exists_analytic_localInverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Filter Metric
open scoped Topology

/-- **Continuity of a global right inverse of an injective entire map.**

If `Ψ : ℂ → ℂ` is differentiable everywhere and injective on an open set `U`, and `g` is any
function that is a right inverse of `Ψ` on `Ψ '' U` (i.e. `Ψ (g y) = y` with `g y ∈ U` whenever
`y ∈ Ψ '' U`), then `g` is continuous at every point `Ψ x` with `x ∈ U`.

The point is that near such a point `Ψ x` the set `Ψ '' U` contains a neighbourhood of `Ψ x`:
the local holomorphic inverse `σ` produced by `Work.ELRig.LocalInverse.exists_analytic_localInverse`
is continuous, so it maps a small ball around `Ψ x` into `U`, where it inverts `Ψ`; on that ball
`g` and `σ` agree by injectivity of `Ψ` on `U`. -/
theorem continuousAt_invOn {U : Set ℂ} (hU : IsOpen U) {Ψ : ℂ → ℂ} (hΨ : Differentiable ℂ Ψ)
    (hinj : Set.InjOn Ψ U) {g : ℂ → ℂ} (hg : ∀ y ∈ Ψ '' U, Ψ (g y) = y ∧ g y ∈ U) {x : ℂ}
    (hx : x ∈ U) : ContinuousAt g (Ψ x) := by
  -- a ball around `x` contained in `U`
  obtain ⟨r, hrpos, hrU⟩ := (Metric.isOpen_iff.mp hU) x hx
  have hinjr : Set.InjOn Ψ (Metric.ball x r) := fun a ha b hb h => hinj (hrU ha) (hrU hb) h
  -- a local analytic inverse `σ` of `Ψ` near `Ψ x`
  obtain ⟨δ₁, hδ₁pos, δ₂, hδ₂pos, σ, hσan, hσright, hσleft, -⟩ :=
    LocalInverse.exists_analytic_localInverse hΨ ⟨r, hrpos, hinjr⟩
  have hσcont : ContinuousAt σ (Ψ x) :=
    (hσan (Ψ x) (Metric.mem_ball_self hδ₂pos)).continuousAt
  have hσx : σ (Ψ x) = x := hσleft x (Metric.mem_ball_self hδ₁pos)
  -- `σ` maps a neighbourhood of `Ψ x` into `U`, and inverts `Ψ` there
  have hσU : ∀ᶠ z in 𝓝 (Ψ x), σ z ∈ U :=
    hσcont.preimage_mem_nhds (by rw [hσx]; exact hU.mem_nhds hx)
  have hball : Metric.ball (Ψ x) δ₂ ∈ 𝓝 (Ψ x) := Metric.ball_mem_nhds _ hδ₂pos
  have hev : ∀ᶠ z in 𝓝 (Ψ x), σ z ∈ U ∧ z ∈ Metric.ball (Ψ x) δ₂ := hσU.and hball
  -- on a neighbourhood of `Ψ x`, `g` agrees with `σ`
  have hcongr : σ =ᶠ[𝓝 (Ψ x)] g := by
    obtain ⟨B, hBpos, hBsub⟩ := Metric.mem_nhds_iff.mp hev
    filter_upwards [Metric.ball_mem_nhds (Ψ x) hBpos] with z hz
    obtain ⟨hσUz, hzball⟩ := hBsub hz
    -- `z = Ψ (σ z)` with `σ z ∈ U`, so `z ∈ Ψ '' U` and `g z` is computed there
    have hzimg : z ∈ Ψ '' U := ⟨σ z, hσUz, hσright z hzball⟩
    obtain ⟨hgz, hgzU⟩ := hg z hzimg
    exact (hinj hgzU hσUz (by rw [hgz, hσright z hzball])).symm
  exact hσcont.congr hcongr

end Work.ELRig
