import Mathlib
import Submission.Work.C17g.convex_hull_segments
import Submission.Work.C17g.holo_lipschitz_compact

namespace Work.C17g

open Set Metric MeasureTheory intervalIntegral

/--
**Lipschitz bound for the holomorphic integrand along a segment.**

Let `S ⊆ ℂ` be open and convex, `z₀ ∈ S`, and `f : ℂ → E` complex differentiable on `S`
(`E` an arbitrary (possibly incomplete) complex normed space).  For every `z ∈ S` there are
`ρ > 0` and an interval-integrable `bound : ℝ → ℝ` such that `ball z ρ ⊆ S` and, for every
`t ∈ [0,1]`, the map
`x ↦ (x - z₀) • f (z₀ + t • (x - z₀))`
is Lipschitz on `ball z ρ` with constant `Real.nnabs (bound t)`.

The proof uses the compact set `T` produced by `convex_hull_segments` (containing `ball z ρ`
and closed under `w ↦ z₀ + t • (w - z₀)` for `t ∈ [0,1]`), on which `f` is Lipschitz
(`holo_lipschitz_compact`) and bounded.  A single constant `C = R * Kf + N` then bounds the
Lipschitz constant of the integrand for all `t`, so `bound` may be taken constant.
-/
theorem integrand_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set ℂ} (hS : Convex ℝ S) (hSo : IsOpen S) {z₀ : ℂ} (hz₀ : z₀ ∈ S)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f S) (z : ℂ) (hz : z ∈ S) :
    ∃ (ρ : ℝ) (bound : ℝ → ℝ), 0 < ρ ∧ Metric.ball z ρ ⊆ S ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1,
        LipschitzOnWith (Real.nnabs (bound t))
          (fun x : ℂ => (x - z₀) • f (z₀ + t • (x - z₀))) (Metric.ball z ρ)) ∧
      IntervalIntegrable bound volume (0:ℝ) 1 := by
  -- `S` is a neighbourhood of `z`; pick `ρ > 0` with `closedBall z ρ ⊆ S`.
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hSo z hz
  set ρ : ℝ := ε / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hcball : Metric.closedBall z ρ ⊆ S := fun x hx =>
    hεS (Metric.closedBall_subset_ball (by rw [hρdef]; linarith) hx)
  have hball : Metric.ball z ρ ⊆ S := fun x hx => hcball (Metric.ball_subset_closedBall hx)
  -- The compact set `T` containing `ball z ρ` and stable under `w ↦ z₀ + t • (w - z₀)`.
  obtain ⟨T, hTcomp, hTne, hz₀T, hballT, hTS, hTclosed⟩ :=
    convex_hull_segments hS hz₀ hz hρ hcball
  -- `f` is Lipschitz on `T` ...
  obtain ⟨Kf, hKf⟩ := holo_lipschitz_compact hSo hf hTcomp hTS
  -- ... and bounded on `T`.
  have hcont : ContinuousOn f T := hf.continuousOn.mono hTS
  obtain ⟨N, hN⟩ := hTcomp.exists_bound_of_continuousOn hcont
  have hN0 : 0 ≤ N := by
    obtain ⟨w, hw⟩ := hTne
    exact (norm_nonneg _).trans (hN w hw)
  -- `R` bounds `‖x - z₀‖` on `ball z ρ`.
  set R : ℝ := ρ + ‖z - z₀‖ with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; linarith [norm_nonneg (z - z₀)]
  have hRbd : ∀ x ∈ Metric.ball z ρ, ‖x - z₀‖ ≤ R := by
    intro x hx
    have h1 : ‖x - z‖ < ρ := by
      have h2 := Metric.mem_ball.mp hx
      rwa [dist_eq_norm] at h2
    calc ‖x - z₀‖ = ‖(x - z) + (z - z₀)‖ := by
            rw [show x - z₀ = (x - z) + (z - z₀) by ring]
      _ ≤ ‖x - z‖ + ‖z - z₀‖ := norm_add_le _ _
      _ ≤ R := by rw [hRdef]; linarith
  -- The uniform Lipschitz constant.
  set C : ℝ := R * (Kf : ℝ) + N with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact add_nonneg (mul_nonneg hR0 Kf.coe_nonneg) hN0
  refine ⟨ρ, fun _ => C, hρ, hball, ?_, intervalIntegrable_const⟩
  intro t ht
  rw [Real.nnabs_of_nonneg hC0, Real.toNNReal_of_nonneg hC0]
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  simp only [NNReal.coe_mk]
  rw [dist_eq_norm, dist_eq_norm]
  have hxT : x ∈ T := hballT hx
  have hyT : y ∈ T := hballT hy
  have haxT : z₀ + t • (x - z₀) ∈ T := hTclosed x hxT t ht
  have hayT : z₀ + t • (y - z₀) ∈ T := hTclosed y hyT t ht
  have hlip := hKf.dist_le_mul (z₀ + t • (x - z₀)) haxT (z₀ + t • (y - z₀)) hayT
  -- Lipschitz bound for the inner factor `f ∘ (segment)`.
  have hnorm : ‖f (z₀ + t • (x - z₀)) - f (z₀ + t • (y - z₀))‖ ≤ (Kf : ℝ) * ‖x - y‖ := by
    have hsub2 : (z₀ + t • (x - z₀)) - (z₀ + t • (y - z₀)) = t • (x - y) := by
      rw [add_sub_add_left_eq_sub, ← smul_sub]
      congr 1
      ring
    calc ‖f (z₀ + t • (x - z₀)) - f (z₀ + t • (y - z₀))‖
        ≤ (Kf : ℝ) * ‖(z₀ + t • (x - z₀)) - (z₀ + t • (y - z₀))‖ := by
          simpa only [dist_eq_norm] using hlip
      _ = (Kf : ℝ) * (t * ‖x - y‖) := by
          rw [hsub2, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ (Kf : ℝ) * ‖x - y‖ := by
          refine mul_le_mul_of_nonneg_left ?_ Kf.coe_nonneg
          calc t * ‖x - y‖ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
            _ = ‖x - y‖ := one_mul _
  -- Decompose the difference of the integrand values.
  have hgrp : (x - z₀) • f (z₀ + t • (x - z₀)) - (y - z₀) • f (z₀ + t • (y - z₀))
      = (x - z₀) • (f (z₀ + t • (x - z₀)) - f (z₀ + t • (y - z₀)))
        + (x - y) • f (z₀ + t • (y - z₀)) := by
    rw [smul_sub]
    module
  rw [hgrp]
  calc ‖(x - z₀) • (f (z₀ + t • (x - z₀)) - f (z₀ + t • (y - z₀)))
          + (x - y) • f (z₀ + t • (y - z₀))‖
      ≤ ‖(x - z₀) • (f (z₀ + t • (x - z₀)) - f (z₀ + t • (y - z₀)))‖
          + ‖(x - y) • f (z₀ + t • (y - z₀))‖ := norm_add_le _ _
    _ ≤ R * ((Kf : ℝ) * ‖x - y‖) + ‖x - y‖ * N := by
          rw [norm_smul, norm_smul]
          exact add_le_add
            (mul_le_mul (hRbd x hx) hnorm (norm_nonneg _) hR0)
            (mul_le_mul_of_nonneg_left (hN _ hayT) (norm_nonneg _))
    _ = C * ‖x - y‖ := by rw [hCdef]; ring

end Work.C17g
