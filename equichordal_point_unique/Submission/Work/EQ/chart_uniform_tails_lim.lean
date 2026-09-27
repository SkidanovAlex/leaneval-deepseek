import Mathlib
import Submission.Work.EQ.chart_uniform_tails

/-! # Uniform principal tails of a chart with a finite `ψ₂`-limit

`Work.EQ.chart_uniform_tails` needs an explicit bound on `ψ₂ ∘ e` near `0`.  A chart of a *genuine
puncture* only comes with a finite limit `ψ₂ ∘ e → v₀`, which however supplies such a bound
(`Tendsto.eventually`).  This is the form used by the assembly of
`Work.EQ.countable_puncture_psi1_limits`. -/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

/-- **Uniform principal tails of a chart, from a finite `ψ₂`-limit.** -/
theorem chart_uniform_tails_lim {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u₀ v₀ : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u₀ k)
    (hv : Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ N : ℕ, ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < δ →
      (∀ n : ℕ, N ≤ n → (e ζ).1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * (e ζ).2.1)) ∧
      (∀ n : ℕ, N ≤ n → (e ζ).1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * (e ζ).2.2)) := by
  have hbdd : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < δ →
      ‖(e ζ).2.2‖ ≤ ‖v₀‖ + 1 := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp
      (hv (Metric.ball_mem_nhds v₀ (by norm_num : (0 : ℝ) < 1)))
    refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun ζ hζ0 hζlt => ?_⟩
    have hζδ : ζ ∈ Metric.ball (0 : ℂ) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hζlt (min_le_left _ _)
    have hζne : ζ ∈ ({(0 : ℂ)}ᶜ : Set ℂ) := by
      simpa using hζ0.ne'
    have h1 := hsub ⟨hζδ, hζne⟩
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h1
    have h2 : ‖(e ζ).2.2‖ - ‖v₀‖ ≤ ‖(e ζ).2.2 - v₀‖ := norm_sub_norm_le _ _
    linarith [h1, h2]
  obtain ⟨δ, hδ, hle, N, hN⟩ := chart_uniform_tails ha0 ha1 hh he
    (by obtain ⟨δ', hδ', hle', hb⟩ := hbdd; exact ⟨δ', hδ', hle', ‖v₀‖ + 1, hb⟩)
  exact ⟨δ, hδ, hle, N, hN⟩

end

end Work.EQ
