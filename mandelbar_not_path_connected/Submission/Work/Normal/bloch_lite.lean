import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

open Metric Set Function

/-- A quantitative "lite" form of Bloch's theorem: a holomorphic function on the unit
ball with `F 0 = 0`, `F' 0 = 1` and `‖F'‖ ≤ 2` covers the disc of radius `1/16`, with a
preimage in the closed disc of radius `1/4`.

The proof bounds `‖F' z - 1‖ ≤ 3‖z‖` by the Schwarz lemma (applied to `deriv F - 1`, which
is holomorphic by Cauchy's theorem), whence `Ψ z = z - F z` is `3/4`-Lipschitz on
`closedBall 0 (1/4)` with `Ψ 0 = 0`.  Then `z ↦ a + Ψ z` is a `3/4`-contraction of that disc
into itself for `‖a‖ < 1/16`, and the Banach fixed point theorem produces `w` with `F w = a`. -/
theorem bloch_lite {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (h0 : F 0 = 0) (h1 : deriv F 0 = 1) (h2 : ∀ z ∈ Metric.ball 0 1, ‖deriv F z‖ ≤ 2) :
    ∀ a : ℂ, ‖a‖ < (1/16 : ℝ) →
      ∃ w : ℂ, w ∈ Metric.closedBall 0 (1/4 : ℝ) ∧ F w = a := by
  intro a ha
  -- (1) `deriv F` is holomorphic on the unit ball.
  have hdF' : DifferentiableOn ℂ (deriv F) (Metric.ball 0 1) := hF.deriv Metric.isOpen_ball
  -- (2) Schwarz lemma applied to `z ↦ deriv F z - 1`, which lands in `closedBall 0 3`.
  have hGzero : (fun z => deriv F z - 1) 0 = 0 := by simp [h1]
  have hGdiff : DifferentiableOn ℂ (fun z => deriv F z - 1) (Metric.ball 0 1) :=
    hdF'.sub_const 1
  have hGmaps : MapsTo (fun z => deriv F z - 1) (Metric.ball 0 1)
      (Metric.closedBall ((fun z => deriv F z - 1) 0) 3) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, hGzero, sub_zero]
    show ‖deriv F z - 1‖ ≤ 3
    calc ‖deriv F z - 1‖ ≤ ‖deriv F z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 + 1 := by
          rw [norm_one]
          linarith [h2 z hz]
      _ = 3 := by norm_num
  have hSchwarz : ∀ z ∈ Metric.ball 0 1, ‖deriv F z - 1‖ ≤ 3 * ‖z‖ := by
    intro z hz
    have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball (c := 0) (R₁ := 1) (R₂ := 3)
      hGdiff hGmaps hz
    simp only [dist_eq_norm, h1, sub_self, sub_zero, div_one] at h
    exact h
  -- (3) `Ψ z = z - F z` has derivative `1 - deriv F z`.
  set Ψ : ℂ → ℂ := fun z => z - F z with hΨdef
  have hPsi0 : Ψ 0 = 0 := by simp [hΨdef, h0]
  have hΨderiv : ∀ z ∈ Metric.ball 0 1, deriv Ψ z = 1 - deriv F z := by
    intro z hz
    have hFz : DifferentiableAt ℂ F z := hF.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have h : deriv (id - F) z = 1 - deriv F z := by
      rw [deriv_sub differentiableAt_id hFz, deriv_id]
    rw [hΨdef]
    exact h
  have hzmem : ∀ z ∈ Metric.closedBall (0 : ℂ) (1/4 : ℝ), z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff]
    linarith
  have hΨdiffAt : ∀ z ∈ Metric.closedBall (0 : ℂ) (1/4 : ℝ), DifferentiableAt ℂ Ψ z := by
    intro z hz
    have hFz : DifferentiableAt ℂ F z :=
      hF.differentiableAt (Metric.isOpen_ball.mem_nhds (hzmem z hz))
    rw [hΨdef]
    exact differentiableAt_id.sub hFz
  have hΨbnd : ∀ z ∈ Metric.closedBall (0 : ℂ) (1/4 : ℝ), ‖deriv Ψ z‖ ≤ 3/4 := by
    intro z hz
    rw [hΨderiv z (hzmem z hz), norm_sub_rev]
    have hzr : ‖z‖ ≤ 1/4 := mem_closedBall_zero_iff.mp hz
    calc ‖deriv F z - 1‖ ≤ 3 * ‖z‖ := hSchwarz z (hzmem z hz)
      _ ≤ 3 * (1/4) := by linarith
      _ = 3/4 := by norm_num
  -- (4) `Ψ` is `3/4`-Lipschitz on `closedBall 0 (1/4)`.
  have hLip : ∀ x ∈ Metric.closedBall (0 : ℂ) (1/4 : ℝ),
      ∀ y ∈ Metric.closedBall (0 : ℂ) (1/4 : ℝ), ‖Ψ y - Ψ x‖ ≤ (3/4) * ‖y - x‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_deriv_le (fun z hz => hΨdiffAt z hz)
      (fun z hz => hΨbnd z hz) (convex_closedBall (0 : ℂ) (1/4)) hx hy
  -- (5) The contraction `φ z = a + Ψ z` of `closedBall 0 (1/4)`.
  set φ : ℂ → ℂ := fun z => a + Ψ z with hφdef
  have hφmaps : MapsTo φ (Metric.closedBall (0 : ℂ) (1/4 : ℝ))
      (Metric.closedBall (0 : ℂ) (1/4 : ℝ)) := by
    intro z hz
    have hzr : ‖z‖ ≤ 1/4 := mem_closedBall_zero_iff.mp hz
    have hz0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (1/4 : ℝ) :=
      Metric.mem_closedBall_self (by norm_num)
    have hbound := hLip 0 hz0 z hz
    rw [hPsi0, sub_zero, sub_zero] at hbound
    rw [mem_closedBall_zero_iff]
    calc ‖φ z‖ = ‖a + Ψ z‖ := by rw [hφdef]
      _ ≤ ‖a‖ + ‖Ψ z‖ := norm_add_le _ _
      _ ≤ 1/16 + 3/4 * (1/4) := by linarith
      _ = 1/4 := by norm_num
  have hContr : ContractingWith (3/4 : NNReal)
      (hφmaps.restrict φ (Metric.closedBall (0 : ℂ) (1/4 : ℝ))
        (Metric.closedBall (0 : ℂ) (1/4 : ℝ))) := by
    refine ⟨by norm_num, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hxy := hLip (x : ℂ) x.2 (y : ℂ) y.2
    show dist (φ (x : ℂ)) (φ (y : ℂ)) ≤ (3/4 : ℝ) * dist (x : ℂ) (y : ℂ)
    rw [dist_eq_norm, dist_eq_norm]
    have hφxy : φ (x : ℂ) - φ (y : ℂ) = -(Ψ (y : ℂ) - Ψ (x : ℂ)) := by
      show a + Ψ (x : ℂ) - (a + Ψ (y : ℂ)) = -(Ψ (y : ℂ) - Ψ (x : ℂ))
      ring
    rw [hφxy, norm_neg, norm_sub_rev (x : ℂ) (y : ℂ)]
    exact hxy
  -- (6) Banach fixed point theorem.
  have hsc : IsComplete (Metric.closedBall (0 : ℂ) (1/4 : ℝ)) :=
    (Metric.isClosed_closedBall).isComplete
  obtain ⟨w, hws, hwfix, -⟩ := hContr.exists_fixedPoint' hsc hφmaps
    (x := (0 : ℂ)) (Metric.mem_closedBall_self (by norm_num)) (edist_ne_top _ _)
  refine ⟨w, hws, ?_⟩
  have hφw : φ w = a + (w - F w) := by simp [hφdef, hΨdef]
  have heq : a + (w - F w) = w := by
    rw [← hφw]
    exact Function.IsFixedPt.eq hwfix
  linear_combination -heq

end Work.Normal
