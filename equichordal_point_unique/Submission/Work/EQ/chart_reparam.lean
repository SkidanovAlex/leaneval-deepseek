import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_fibre_defs

/-! # Reparametrising a punctured chart by a dilation `ζ ↦ c ζ`

Reparametrising a chart `e` (`ψ₁ ∘ e = u₀ + κ ζ^k`) by `ζ ↦ c ζ` (`c ≠ 0`) leaves it a chart at the
same centre `u₀`, with scale `κ c^k`; it preserves genuineness and the `ψ₂`-limit, but shrinks the
`ζ`-domain, which lets the uniform tails be assumed on the *whole* punctured unit disc (needed by
`Work.EQ.genuine_chart_window_degenerate`). -/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

/-- **A dilation of the chart variable leaves a punctured chart a punctured chart.** -/
theorem isPuncturedChart_comp_mul {a : ℝ} {h : ℂ → ℂ} {e : ℂ → ChainData} {u₀ : ℂ} {k : ℕ}
    {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) (he : IsPuncturedChart a h e u₀ k) :
    IsPuncturedChart a h (fun ζ => e (c * ζ)) u₀ k := by
  obtain ⟨hk, hu₀, κ, hκ, hmem, hinj, hcont, hmer, hmern⟩ := he
  have hball : ∀ ζ : ℂ, ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} →
      c * ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro ζ hζ
    rw [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff] at hζ
    rw [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
    refine ⟨?_, mul_ne_zero hc hζ.2⟩
    calc ‖c * ζ‖ = ‖c‖ * ‖ζ‖ := norm_mul _ _
      _ ≤ 1 * ‖ζ‖ := mul_le_mul_of_nonneg_right hc1 (norm_nonneg ζ)
      _ = ‖ζ‖ := one_mul ‖ζ‖
      _ < 1 := hζ.1
  refine ⟨hk, hu₀, κ * c ^ k, mul_ne_zero hκ (pow_ne_zero _ hc), ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    obtain ⟨hH0, hpsi⟩ := hmem _ (hball ζ hζ)
    refine ⟨hH0, ?_⟩
    rw [hpsi]
    ring
  · rintro ζ hζ ζ' hζ' heq
    exact mul_left_cancel₀ hc (hinj (hball ζ hζ) (hball ζ' hζ') heq)
  · refine hcont.comp (continuous_const.mul continuous_id).continuousOn (fun ζ _ => ?_)
    exact hball ζ (by simpa using ‹ζ ∈ Metric.ball (0 : ℂ) 1 \ {0}›)
  · refine MeromorphicAt.comp_analyticAt (x := 0) (g := fun ζ : ℂ => c * ζ)
      (f := fun u : ℂ => (e u).2.2) ?_ ?_
    · rw [mul_zero]; exact hmer
    · exact analyticAt_const.mul analyticAt_id
  · intro n
    refine ⟨?_, ?_⟩
    · refine MeromorphicAt.comp_analyticAt (x := 0) (g := fun ζ : ℂ => c * ζ)
        (f := fun u : ℂ => ((e u).1 n).1) ?_ ?_
      · rw [mul_zero]; exact (hmern n).1
      · exact analyticAt_const.mul analyticAt_id
    · refine MeromorphicAt.comp_analyticAt (x := 0) (g := fun ζ : ℂ => c * ζ)
        (f := fun u : ℂ => ((e u).1 n).2) ?_ ?_
      · rw [mul_zero]; exact (hmern n).2
      · exact analyticAt_const.mul analyticAt_id

/-- **A dilation of the chart variable preserves the `ψ₂`-limit.** -/
theorem chart_comp_mul_psi2 {e : ℂ → ChainData} {v₀ : ℂ} {c : ℂ} (hc : c ≠ 0)
    (hv : Filter.Tendsto (fun u : ℂ => (e u).2.2)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀)) :
    Filter.Tendsto (fun ζ : ℂ => (e (c * ζ)).2.2)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀) := by
  have h1 : Filter.Tendsto (fun ζ : ℂ => c * ζ) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ))
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc0 : ContinuousAt (fun ζ : ℂ => c * ζ) 0 :=
        continuousAt_const.mul continuousAt_id
      simpa using hc0.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ζ hζ
      show c * ζ ≠ 0
      exact mul_ne_zero hc hζ
  exact hv.comp h1

/-- **A dilation of the chart variable preserves genuineness.** -/
theorem chart_comp_mul_genuine {a : ℝ} {h : ℂ → ℂ} {e : ℂ → ChainData} {c : ℂ} (hc : c ≠ 0)
    (hgen : ¬ ∃ q ∈ H0 a h, Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) :
    ¬ ∃ q ∈ H0 a h, Filter.Tendsto (fun ζ : ℂ => e (c * ζ))
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q) := by
  rintro ⟨q, hq, hlim⟩
  refine hgen ⟨q, hq, ?_⟩
  have h1 : Filter.Tendsto (fun u : ℂ => u / c) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ))
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc0 : ContinuousAt (fun u : ℂ => u / c) 0 := continuousAt_id.div_const c
      simpa using hc0.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact div_ne_zero hu hc
  have h2 := hlim.comp h1
  refine h2.congr' (Filter.Eventually.of_forall fun u => ?_)
  show e (c * (u / c)) = e u
  rw [mul_div_cancel₀ u hc]

end

end Work.EQ
