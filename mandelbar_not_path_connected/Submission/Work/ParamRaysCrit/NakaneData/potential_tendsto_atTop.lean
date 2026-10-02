import Mathlib
import Submission.Work.ParamRays.MbDefs
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Interface

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRaysCrit.NakaneData

/-- **The parameter potential tends to `+∞` at infinity.**  For every `t` there is `R` such that
`t ≤ potential c` for every `‖c‖ ≥ R` (the last clause of `Work.Top.NakaneData` at
`Mb = Work.ParamRays.Mb`, `Φ = Work.ParamRays.Phi`, which is what makes the parameter-plane
Nakane data non-vacuous).

Route.  `Work.ParamRays.Phi_isBigO_atTop h : Φ c / c → 1` as `c → ∞` (cocompactly), so for `‖c‖`
large `‖Φ c‖ ≥ ‖c‖ / 2`; and `Work.ParamRays.mandelbar_subset_closedBall` gives
`Mb ⊆ Metric.closedBall 0 2`, so for `‖c‖ ≥ 3` one has `c ∉ Mb` and
`potential c = Real.log ‖Phi c‖ ≥ Real.log (‖c‖ / 2) ≥ t` once `‖c‖ ≥ 2 * Real.exp t`.
The compact set of the cocompact statement is handled with `Filter.mem_cocompact` and
`Bornology.IsBounded.subset_closedBall`. -/
theorem potential_tendsto_atTop (h : Work.ParamRays.NakaneInput) (t : ℝ) :
    ∃ R : ℝ, ∀ c : ℂ, R ≤ ‖c‖ → t ≤ Work.ParamRays.potential c := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  -- `Φ c / c → 1`, so the set where `‖Φ c / c - 1‖ < 1/2` is a neighbourhood of infinity.
  have hS : {c : ℂ | ‖Work.ParamRays.Phi c / c - 1‖ < (1 / 2 : ℝ)} ∈ Filter.cocompact ℂ := by
    have h0 := Work.ParamRays.Phi_isBigO_atTop h (Metric.ball_mem_nhds 1 hhalf)
    have hset : {c : ℂ | ‖Work.ParamRays.Phi c / c - 1‖ < (1 / 2 : ℝ)}
        = (fun c : ℂ => Work.ParamRays.Phi c / c) ⁻¹' Metric.ball 1 (1 / 2) := by
      ext c
      simp [Metric.mem_ball, dist_eq_norm]
    rw [hset]
    exact h0
  rw [Filter.mem_cocompact] at hS
  obtain ⟨K, hKcpt, hKsub⟩ := hS
  obtain ⟨r, hr⟩ := hKcpt.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max 3 (max (r + 1) (2 * Real.exp t)), ?_⟩
  intro c hc
  have hc3 : (3 : ℝ) ≤ ‖c‖ := le_trans (le_max_left _ _) hc
  have hcr : r + 1 ≤ ‖c‖ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hc
  have hce : 2 * Real.exp t ≤ ‖c‖ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hc
  -- large `c` lies outside the mandelbar
  have hcMb : c ∉ Work.ParamRays.Mb := by
    intro hmem
    have h2 := Work.ParamRays.mandelbar_subset_closedBall hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    linarith
  -- large `c` lies outside the compact set, hence in the good set
  have hcS : ‖Work.ParamRays.Phi c / c - 1‖ < (1 / 2 : ℝ) := by
    have hcK : c ∉ K := by
      intro hcK
      have h2 := hr hcK
      rw [Metric.mem_closedBall, dist_zero_right] at h2
      linarith
    exact hKsub hcK
  rw [Work.ParamRays.potential, dif_neg hcMb]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0] at hc3
    simp only [norm_zero] at hc3
    linarith
  -- `‖Φ c / c‖ ≥ 1 - 1/2 = 1/2`, hence `‖Φ c‖ ≥ ‖c‖ / 2`
  have h1 : (1 / 2 : ℝ) ≤ ‖Work.ParamRays.Phi c / c‖ := by
    have h2 := abs_norm_sub_norm_le (Work.ParamRays.Phi c / c) (1 : ℂ)
    rw [norm_one] at h2
    have h3 := (abs_le.mp h2).1
    linarith
  have hnorm : ‖Work.ParamRays.Phi c‖ = ‖Work.ParamRays.Phi c / c‖ * ‖c‖ := by
    rw [← norm_mul, div_mul_cancel₀ _ hc0]
  have hlower : ‖c‖ / 2 ≤ ‖Work.ParamRays.Phi c‖ := by
    rw [hnorm]
    nlinarith [norm_nonneg c, h1]
  have hlog : Real.log (‖c‖ / 2) ≤ Real.log ‖Work.ParamRays.Phi c‖ :=
    Real.log_le_log (by linarith) hlower
  have hlog2 : t ≤ Real.log (‖c‖ / 2) := by
    have h2 : Real.exp t ≤ ‖c‖ / 2 := by linarith
    have := Real.log_le_log (Real.exp_pos t) h2
    rwa [Real.log_exp] at this
  linarith

end Work.ParamRaysCrit.NakaneData
