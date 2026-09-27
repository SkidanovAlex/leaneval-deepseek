import Mathlib
import Submission.Work.EQ.EquiLocalDefs
import Submission.Work.EQ.chart_norm_bound_pow
import Submission.Work.EQ.chart_eq_at_interior

namespace Work.EQ

open Filter _root_.Topology

/-- **The set of `ζ` whose leg point lies on the other leg is closed in the orbit domain (second
half of the dichotomy).**  Same setting as `Work.EQ.chart_leg_meets_open`: `E`, `F` are chart data
with the same centre `u₁`, `ρ > 0` is small (`hsmallE`, `hsmallF`), and moreover `ρ ≤ ‖κ'‖/2`.
If `ζ` with `ζ ≠ 0`, `‖κ ζ^k‖ < ρ` lies in the closure of
`S := {ζ' ≠ 0 | ‖κ ζ'^k‖ < ρ ∧ E ζ' ∈ F '' {η ≠ 0 | ‖κ' η^{k'}‖ < ρ}}`, then `E ζ` itself lies on
the `F`-leg: `E ζ ∈ F '' {η ≠ 0 | ‖κ' η^{k'}‖ < ρ}`.

Route: take `ζ_n ∈ S` with `ζ_n → ζ`.  Write `E ζ_n = F η_n` with `η_n ≠ 0`,
`‖κ' η_n^{k'}‖ < ρ`.  Then `‖κ' η_n^{k'}‖ = ‖κ ζ_n^k‖` (chart formulas, using `hsmallE`/`hsmallF`),
so `‖η_n‖ < 1` because `ρ ≤ ‖κ'‖/2`, and the sequence `η_n` has a convergent subsequence
`η_{φ n} → η*` in the compact closed unit ball (`IsCompact.tendsto_subseq`).  Then
`‖κ' (η*)^{k'}‖ = ‖κ ζ^k‖ < ρ` (limits of both sides, `ζ ≠ 0`), so `η* ≠ 0` and `‖η*‖ < 1` (again
`ρ ≤ ‖κ'‖/2`), the chart `F` is continuous at `η*`, `E` is continuous at `ζ`, and
`F η* = E ζ` follows by passing `F η_{φ n} = E ζ_{φ n}` to the limit. -/
theorem chart_leg_meets_closed {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) {u₁ : ℂ}
    {E F : ℂ → ChainData} {κ κ' : ℂ} {k k' : ℕ} (hE : IsChartData a h E u₁ κ k)
    (hF : IsChartData a h F u₁ κ' k') {ρ : ℝ} (hρ : 0 < ρ)
    (hsmallE : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ * ζ ^ k = u → ‖ζ‖ < 1)
    (hsmallF : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ' * ζ ^ k' = u → ‖ζ‖ < 1)
    (hbdF : ρ ≤ ‖κ'‖ / 2)
    {ζ : ℂ} (hζ : ζ ≠ 0) (hζρ : ‖κ * ζ ^ k‖ < ρ)
    (hcl : ζ ∈ closure {ζ' : ℂ | ζ' ≠ 0 ∧ ‖κ * ζ' ^ k‖ < ρ ∧
        E ζ' ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ}}) :
    E ζ ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ} := by
  have hκ : κ ≠ 0 := hE.2.1
  have hκ' : κ' ≠ 0 := hF.2.1
  have hk' : 0 < k' := hF.1
  -- `ζ` is an interior point of the chart domain of `E`
  have hζsmall : ‖ζ‖ < 1 :=
    hsmallE (u₁ + κ * ζ ^ k) ζ (by simpa using hζρ) rfl
  -- the parameters of `S` approaching `ζ`, and their partners on the `F`-leg
  obtain ⟨ζs, hζs_mem, hζs_lim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hζs_ne : ∀ n, ζs n ≠ 0 := fun n => (hζs_mem n).1
  have hζs_ρ : ∀ n, ‖κ * ζs n ^ k‖ < ρ := fun n => (hζs_mem n).2.1
  have hζs_small : ∀ n, ‖ζs n‖ < 1 := fun n =>
    hsmallE (u₁ + κ * ζs n ^ k) (ζs n) (by simpa using hζs_ρ n) rfl
  have hex : ∀ n, ∃ η : ℂ, η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ ∧ F η = E (ζs n) := fun n => by
    obtain ⟨η, hηmem, hηeq⟩ := (hζs_mem n).2.2
    exact ⟨η, hηmem.1, hηmem.2, hηeq⟩
  choose ηs hηs_ne hηs_ρ hηs_eq using hex
  have hηs_small : ∀ n, ‖ηs n‖ < 1 := fun n => chart_norm_bound_pow hκ' hk' (hηs_ρ n) hbdF
  -- the chart identity `κ' ηₙ^{k'} = κ ζₙ^k` along the sequence
  have hkey : ∀ n, κ' * ηs n ^ k' = κ * ζs n ^ k := fun n => by
    have h1 : (F (ηs n)).2.1 = u₁ + κ' * ηs n ^ k' :=
      (chart_eq_at_interior hF (hηs_ne n) (hηs_small n)).1
    have h2 : (E (ζs n)).2.1 = u₁ + κ * ζs n ^ k :=
      (chart_eq_at_interior hE (hζs_ne n) (hζs_small n)).1
    have h3 : (F (ηs n)).2.1 = (E (ζs n)).2.1 := by rw [hηs_eq n]
    rw [h1, h2] at h3
    exact add_left_cancel h3
  -- the partners lie in the compact closed unit ball, so a subsequence converges
  have hηs_ball : ∀ n, ηs n ∈ Metric.closedBall (0 : ℂ) 1 := fun n => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (hηs_small n)
  obtain ⟨η', _, φ, hφmono, hφlim⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : ℂ) 1) hηs_ball
  have hφtend : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hζφlim : Tendsto (ζs ∘ φ) atTop (𝓝 ζ) := hζs_lim.comp hφtend
  -- the chart identity passes to the limit
  have hlimkey : κ' * η' ^ k' = κ * ζ ^ k := by
    have h1 : Tendsto (fun n => κ' * (ηs ∘ φ) n ^ k') atTop (𝓝 (κ' * η' ^ k')) := by
      have hc : Continuous fun z : ℂ => κ' * z ^ k' :=
        continuous_const.mul (continuous_pow k')
      exact (hc.tendsto η').comp hφlim
    have h2 : Tendsto (fun n => κ * (ζs ∘ φ) n ^ k) atTop (𝓝 (κ * ζ ^ k)) := by
      have hc : Continuous fun z : ℂ => κ * z ^ k :=
        continuous_const.mul (continuous_pow k)
      exact (hc.tendsto ζ).comp hζφlim
    refine tendsto_nhds_unique h1 (h2.congr' (Eventually.of_forall fun n => ?_))
    exact (hkey (φ n)).symm
  -- hence `η'` is a non-zero point of the punctured unit disc
  have hη'_ne : η' ≠ 0 := by
    intro h0
    refine mul_ne_zero hκ (pow_ne_zero k hζ) ?_
    rw [← hlimkey, h0, zero_pow hk'.ne', mul_zero]
  have hη'_ρ : ‖κ' * η' ^ k'‖ < ρ := by rw [hlimkey]; exact hζρ
  have hη'_small : ‖η'‖ < 1 := chart_norm_bound_pow hκ' hk' hη'_ρ hbdF
  -- and `F η' = E ζ` by passing the equalities to the limit
  have hFlim : Tendsto (fun n => F (ηs (φ n))) atTop (𝓝 (F η')) :=
    (chart_eq_at_interior hF hη'_ne hη'_small).2.tendsto.comp hφlim
  have hElim : Tendsto (fun n => E (ζs (φ n))) atTop (𝓝 (E ζ)) :=
    (chart_eq_at_interior hE hζ hζsmall).2.tendsto.comp hζφlim
  have hfinal : F η' = E ζ :=
    tendsto_nhds_unique hFlim
      (hElim.congr' (Eventually.of_forall fun n => (hηs_eq (φ n)).symm))
  exact ⟨η', ⟨hη'_ne, hη'_ρ⟩, hfinal⟩

end Work.EQ
