import Mathlib

open Filter
open scoped Topology

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Analysis.PertCrux

/-- If `f z = z + z (z - σ) u z` on the ball of radius `rr` (with `u` bounded by `2` there) and
`‖σ‖ ≤ ρ ≤ rr`, then `f σ = σ`: for `‖σ‖ < rr` this is the normal form at `σ` itself, and for
`‖σ‖ = rr` it follows by continuity of `f` at `σ` (which is interior to `Df`). -/
theorem normalForm_apply_sigma {f : ℂ → ℂ} {Df : Set ℂ} {u : ℂ → ℂ} {σ : ℂ} {ρ rr : ℝ}
    (hρ : 0 < ρ) (hrr : 0 < rr) (hρr : ρ ≤ rr) (hσ : ‖σ‖ ≤ ρ)
    (hDf : IsOpen Df) (hsub : Metric.closedBall (0 : ℂ) ρ ⊆ Df)
    (hfd : DifferentiableOn ℂ f Df)
    (hub : ∀ z ∈ Metric.ball (0 : ℂ) rr, ‖u z‖ ≤ 2)
    (hform : ∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) :
    f σ = σ := by
  -- `σ` lies in `Df`, hence `f` is continuous at `σ`.
  have hσDf : σ ∈ Df :=
    hsub (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hσ))
  have hcont : ContinuousAt f σ := (hfd.differentiableAt (hDf.mem_nhds hσDf)).continuousAt
  -- Work in the filter of points of the ball of radius `rr` tending to `σ`.
  set l := 𝓝[Metric.ball (0 : ℂ) rr] σ with hl
  have hmem : σ ∈ closure (Metric.ball (0:ℂ) rr) := by
    rw [closure_ball 0 (ne_of_gt hrr)]
    exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using le_trans hσ hρr)
  haveI : l.NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem
  -- On the ball, `‖(z - σ)(1 + z u z)‖ ≤ (1 + 2 rr) ‖z - σ‖`.
  have hbound : ∀ᶠ z in l, ‖(z - σ) * (1 + z * u z)‖ ≤ (1 + 2*rr) * ‖z - σ‖ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzr : ‖z‖ < rr := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have huz : ‖u z‖ ≤ 2 := hub z hz
    calc ‖(z - σ) * (1 + z * u z)‖ ≤ ‖z - σ‖ * ‖1 + z * u z‖ := norm_mul_le _ _
      _ ≤ ‖z - σ‖ * (1 + rr * 2) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          have h2 : ‖z * u z‖ ≤ rr * 2 :=
            (norm_mul_le _ _).trans (mul_le_mul hzr.le huz (norm_nonneg _) hrr.le)
          calc ‖1 + z * u z‖ ≤ ‖(1:ℂ)‖ + ‖z * u z‖ := norm_add_le _ _
            _ = 1 + ‖z * u z‖ := by rw [norm_one]
            _ ≤ 1 + rr * 2 := by linarith
      _ = (1 + 2*rr) * ‖z - σ‖ := by ring
  have hC : Tendsto (fun z : ℂ => (1 + 2*rr) * ‖z - σ‖) l (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => z - σ) l (𝓝 0) := by
      have h := (tendsto_id.sub tendsto_const_nhds :
        Tendsto (fun z : ℂ => z - σ) (𝓝 σ) (𝓝 (σ - σ)))
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    simpa using h1.norm.const_mul (1 + 2*rr)
  -- So `z + z (z - σ) u z` tends to `σ` along `l`.
  have hw : Tendsto (fun z : ℂ => (z - σ) * (1 + z * u z)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
      (Filter.Eventually.of_forall (fun z => norm_nonneg _)) hbound
  have h2 : Tendsto (fun z : ℂ => σ + (z - σ) * (1 + z * u z)) l (𝓝 σ) := by
    have h : Tendsto (fun z : ℂ => σ + (z - σ) * (1 + z * u z)) l (𝓝 (σ + 0)) :=
      (tendsto_const_nhds (x := σ)).add hw
    simpa using h
  have hg : Tendsto (fun z : ℂ => z + z * (z - σ) * u z) l (𝓝 σ) :=
    h2.congr (fun z => by ring)
  -- `f` agrees with that expression on the ball, so also `f → σ` along `l`.
  have heq : (fun z : ℂ => z + z * (z - σ) * u z) =ᶠ[l] f := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hform z hz).symm
  have hf' : Tendsto f l (𝓝 σ) := hg.congr' heq
  have hf : Tendsto f l (𝓝 (f σ)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- Uniqueness of limits along the non-trivial filter `l` gives `f σ = σ`.
  exact (tendsto_nhds_unique hf' hf).symm

end Work.Analysis.PertCrux
