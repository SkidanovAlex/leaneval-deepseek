import Mathlib

namespace Work.Whitney

open scoped Topology
open Metric

/-- A smooth map `ψ` which is a "small perturbation of the identity at `0`"
(namely `ψ z = z + G z` with `G` smooth and `fderiv ℝ G 0 = 0`) is injective on a
small ball around `0`, and its Fréchet derivative is injective at every point of
that ball.

This is the local-injectivity ingredient used when deforming an immersion into an
embedding: near a point where the perturbation kills the derivative, the map
`z ↦ z + G z` is a local diffeomorphism-like map (here only local injectivity and
injectivity of the differential are needed, so no completeness of `F` is
required). -/
theorem exists_injOn_ball_of_perturbation
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ψ G : F → F) (hψ : ∀ z, ψ z = z + G z)
    (hG : ContDiff ℝ ⊤ G) (hG0 : fderiv ℝ G 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Set.InjOn ψ (Metric.ball 0 ρ) ∧
      ∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ ψ z) := by
  -- `fderiv G` is continuous, and vanishes at `0`, hence is small on a small ball.
  have hcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by simp)
  have hGdiff : Differentiable ℝ G := hG.differentiable (by simp)
  have hmem : {z : F | fderiv ℝ G z ∈ ball (0 : F →L[ℝ] F) (1 / 2)} ∈ 𝓝 (0 : F) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [hG0]; exact ball_mem_nhds 0 (by norm_num))
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ρ, hρpos, ?_, ?_⟩
  · -- Injectivity of `ψ` on the ball: it is a `1/2`-Lipschitz perturbation of the identity.
    intro x hx y hy hxy
    have h1 : x + G x = y + G y := by simpa [hψ x, hψ y] using hxy
    have h2 : x - y = G y - G x := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm (G y) y]; exact h1
    -- Mean value inequality: `G` is `1/2`-Lipschitz on the ball.
    have hxy2 : ‖x - y‖ ≤ (1 / 2) * ‖y - x‖ := by
      have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
        (s := ball 0 ρ) (f := G) (C := 1 / 2)
        (fun z _ => hGdiff z)
        (fun z hz => by
          have hz' : fderiv ℝ G z ∈ ball (0 : F →L[ℝ] F) (1 / 2) := hρsub hz
          rw [Metric.mem_ball] at hz'
          exact le_of_lt (by simpa [dist_eq_norm] using hz'))
        (convex_ball 0 ρ) hx hy
      calc ‖x - y‖ = ‖G y - G x‖ := by rw [h2]
        _ ≤ 1 / 2 * ‖y - x‖ := hmvt
    have hnorm : ‖x - y‖ = 0 := by
      have hyx : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · -- Injectivity of the differential: `fderiv ψ z = id + fderiv G z` with `‖fderiv G z‖ < 1`.
    intro z hz
    have hfdz : fderiv ℝ ψ z = ContinuousLinearMap.id ℝ F + fderiv ℝ G z := by
      have hψeq : ψ = id + G := by funext w; exact hψ w
      rw [hψeq, fderiv_add (differentiableAt_id) (hGdiff z)]
      congr 1
      exact fderiv_id
    rw [hfdz]
    have hLz : ‖fderiv ℝ G z‖ < 1 / 2 := by
      have hz' : fderiv ℝ G z ∈ ball (0 : F →L[ℝ] F) (1 / 2) := hρsub hz
      rw [Metric.mem_ball] at hz'
      simpa [dist_eq_norm] using hz'
    intro u v huv
    -- `u - v = -(fderiv G z) (u - v)`, hence `‖u - v‖ ≤ (1/2) ‖u - v‖`.
    have h0 : u - v + fderiv ℝ G z (u - v) = 0 := by
      have hthis : (ContinuousLinearMap.id ℝ F + fderiv ℝ G z) (u - v) = 0 := by
        rw [map_sub, huv, sub_self]
      simpa using hthis
    have h1 : u - v = - fderiv ℝ G z (u - v) := eq_neg_of_add_eq_zero_left h0
    have h2 : ‖u - v‖ = ‖fderiv ℝ G z (u - v)‖ := by
      have := congrArg (fun t : F => ‖t‖) h1
      rwa [norm_neg] at this
    have h3 : ‖u - v‖ ≤ 1 / 2 * ‖u - v‖ := by
      calc ‖u - v‖ = ‖fderiv ℝ G z (u - v)‖ := h2
        _ ≤ ‖fderiv ℝ G z‖ * ‖u - v‖ := (fderiv ℝ G z).le_opNorm _
        _ ≤ 1 / 2 * ‖u - v‖ := mul_le_mul_of_nonneg_right hLz.le (norm_nonneg _)
    have hfin : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hfin)

end Work.Whitney
