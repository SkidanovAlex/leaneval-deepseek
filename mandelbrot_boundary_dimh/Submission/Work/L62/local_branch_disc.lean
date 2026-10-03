import Mathlib

/-!
# The local branch of a holomorphic map at a point with nonzero derivative

If `F : ℂ → ℂ` is analytic at `x` and `deriv F x ≠ 0`, then `F` is a local biholomorphism at `x`:
there is a disc `ball (F x) r` on which a (global) inverse branch `ψ` of `F` is defined,
differentiable, sends `F x` back to `x`, takes values in any prescribed open neighbourhood `U`
of `x`, and is injective there.

This is the local inverse function theorem specialised to `ℂ → ℂ`, stated in the exact shape
needed downstream: the inverse is required only to be `DifferentiableOn` a ball (weakest possible
regularity requirement), and the "maps into `U`" clause is absorbed by shrinking the ball
(legitimate because `ψ` is continuous at `F x`).
-/

namespace Work.L62

open Complex Metric Set Filter
open scoped Topology

theorem local_branch_disc {F : ℂ → ℂ} {x : ℂ} (hF : AnalyticAt ℂ F x) (hx : deriv F x ≠ 0)
    {U : Set ℂ} (hUo : IsOpen U) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (Metric.ball (F x) r) ∧
      ψ (F x) = x ∧ (∀ z ∈ Metric.ball (F x) r, F (ψ z) = z) ∧
      Set.MapsTo ψ (Metric.ball (F x) r) U ∧ Set.InjOn ψ (Metric.ball (F x) r) := by
  -- The inverse function theorem: `ψ` is the local inverse of `F` at `x`.
  set ψ : ℂ → ℂ := hF.hasStrictDerivAt.localInverse F (deriv F x) x hx with hψdef
  -- `ψ` is analytic (hence differentiable and continuous) at `F x`.
  have hψ_ana : AnalyticAt ℂ ψ (F x) := by
    rw [hψdef]
    exact hF.analyticAt_localInverse hx
  -- `F` is a right inverse of `ψ` near `F x`, and `ψ (F x) = x`.
  have hright : ∀ᶠ z in 𝓝 (F x), F (ψ z) = z := by
    rw [hψdef]
    exact hF.hasStrictDerivAt.eventually_right_inverse (f := F) (f' := deriv F x) (a := x) hx
  have hleft : ∀ᶠ y in 𝓝 x, ψ (F y) = y := by
    rw [hψdef]
    exact hF.hasStrictDerivAt.eventually_left_inverse (f := F) (f' := deriv F x) (a := x) hx
  have hψ0 : ψ (F x) = x := hleft.self_of_nhds
  -- `ψ` lands in the open set `U` near `F x`.
  have hUev : ∀ᶠ z in 𝓝 (F x), ψ z ∈ U :=
    hψ_ana.continuousAt.eventually (hUo.mem_nhds (by rw [hψ0]; exact hxU))
  -- Turn the three eventual statements into a single radius.
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hright
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.mp hψ_ana.eventually_analyticAt
  obtain ⟨r₃, hr₃, hball₃⟩ := Metric.mem_nhds_iff.mp hUev
  refine ⟨min r₁ (min r₂ r₃), lt_min hr₁ (lt_min hr₂ hr₃), ψ, ?_, hψ0, ?_, ?_, ?_⟩
  · -- differentiability on the ball, from analyticity near `F x`
    intro z hz
    exact (hball₂ (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hz)
      ).differentiableAt.differentiableWithinAt
  · -- right inverse
    intro z hz
    exact hball₁ (Metric.ball_subset_ball (min_le_left _ _) hz)
  · -- values land in `U`
    intro z hz
    exact hball₃ (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _)) hz)
  · -- injectivity, from `F ∘ ψ = id` on the ball
    intro z₁ hz₁ z₂ hz₂ heq
    have h1 : F (ψ z₁) = z₁ := hball₁ (Metric.ball_subset_ball (min_le_left _ _) hz₁)
    have h2 : F (ψ z₂) = z₂ := hball₁ (Metric.ball_subset_ball (min_le_left _ _) hz₂)
    rw [heq] at h1
    exact h1.symm.trans h2

end Work.L62
