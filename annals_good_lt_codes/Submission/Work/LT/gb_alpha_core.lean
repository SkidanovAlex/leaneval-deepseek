import Mathlib

namespace Work.LT

open Filter Real
open scoped Topology

/-- For every `β > 0` there is `α ∈ (0, 1/2]` with `(2e/α)^α ≤ 2^{β/2}` (take `α = 2^{-N}` for large `N`). -/
theorem gb_alpha_core (β : ℝ) (hβ : 0 < β) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 2 ∧
      (2 * Real.exp 1 / α) ^ α ≤ (2 : ℝ) ^ (β / 2) := by
  -- `α ↦ log α * α → 0` as `α → 0⁺`.
  have hlog : Tendsto (fun α : ℝ => Real.log α * α) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
    simpa using h
  -- hence `α ↦ log (2e) * α → 0` as well.
  have hA : Tendsto (fun α : ℝ => Real.log (2 * Real.exp 1) * α) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := (tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi 0)
      (continuous_id.tendsto (0:ℝ))).const_mul (Real.log (2 * Real.exp 1))
    simpa using h
  have hsum : Tendsto (fun α : ℝ => Real.log (2 * Real.exp 1) * α - Real.log α * α)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hA.sub hlog
    simpa using h
  -- `log (2e/α) * α = log (2e) * α - log α * α` for `α > 0`.
  have heq : (fun α : ℝ => Real.log (2 * Real.exp 1 / α) * α) =ᶠ[𝓝[>] (0:ℝ)]
      (fun α => Real.log (2 * Real.exp 1) * α - Real.log α * α) := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hα0 : (0:ℝ) < α := hα
    have h2e : (0:ℝ) < 2 * Real.exp 1 := by positivity
    rw [div_eq_mul_inv, Real.log_mul (ne_of_gt h2e) (inv_ne_zero (ne_of_gt hα0)), Real.log_inv]
    ring
  have hmain : Tendsto (fun α : ℝ => Real.log (2 * Real.exp 1 / α) * α) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    Filter.Tendsto.congr' heq.symm hsum
  have hexp : Tendsto (fun α : ℝ => Real.exp (Real.log (2 * Real.exp 1 / α) * α))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have h2 := (Real.continuous_exp.tendsto 0).comp hmain
    have h : Tendsto (Real.exp ∘ fun α : ℝ => Real.log (2 * Real.exp 1 / α) * α)
        (𝓝[>] (0:ℝ)) (𝓝 1) := by
      simpa only [Real.exp_zero] using h2
    exact h
  -- thus `α ↦ (2e/α)^α → 1` as `α → 0⁺`.
  have hg : Tendsto (fun α : ℝ => (2 * Real.exp 1 / α) ^ α) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    refine hexp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hα0 : (0:ℝ) < α := hα
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < 2 * Real.exp 1 / α)]
  -- `2^{β/2} > 1` since `β > 0`.
  have hc : (1:ℝ) < (2:ℝ) ^ (β / 2) := Real.one_lt_rpow (by norm_num) (by linarith)
  -- All three conditions hold eventually in `𝓝[>] 0`.
  have hev : ∀ᶠ α in 𝓝[>] (0:ℝ),
      0 < α ∧ α ≤ 1 / 2 ∧ (2 * Real.exp 1 / α) ^ α ≤ (2 : ℝ) ^ (β / 2) := by
    have h1 : ∀ᶠ α in 𝓝[>] (0:ℝ), (2 * Real.exp 1 / α) ^ α < (2 : ℝ) ^ (β / 2) :=
      hg.eventually (isOpen_Iio.mem_nhds hc)
    have h2 : ∀ᶠ α in 𝓝[>] (0:ℝ), 0 < α := self_mem_nhdsWithin
    have h3 : ∀ᶠ α in 𝓝[>] (0:ℝ), α ≤ 1 / 2 := by
      have hmem : Set.Iio (1/2:ℝ) ∈ 𝓝[>] (0:ℝ) :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))
      exact Filter.Eventually.mono hmem (fun α h => le_of_lt h)
    filter_upwards [h2, h3, h1] with α hα0 hαh hlt
    exact ⟨hα0, hαh, le_of_lt hlt⟩
  have : (𝓝[>] (0:ℝ)).NeBot := nhdsWithin_Ioi_neBot (a := 0) (b := 0) le_rfl
  obtain ⟨α, h1, h2, h3⟩ := Filter.Eventually.exists hev
  exact ⟨α, h1, h2, h3⟩

end Work.LT
