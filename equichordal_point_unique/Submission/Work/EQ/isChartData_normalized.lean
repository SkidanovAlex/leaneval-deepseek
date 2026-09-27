import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

/-- **Normalising a chart leg.**  Let `E` be chart data over `u₀` with scale `κ ≠ 0` and exponent `k > 0` (`IsChartData a h E u₀ κ k`, i.e. `E` is injective and continuous on the punctured unit disc, maps it into `H0 a h`, and satisfies `(E ζ).2.1 = u₀ + κ ζᵏ` there), and let `ω` be a `k`-th root of `κ` (then `ω ≠ 0`, since `ωᵏ = κ ≠ 0`).  Then the rescaled leg `ζ ↦ E (ζ / ω)` is defined on the punctured disc `{ζ : 0 < ‖ζ‖ < ‖ω‖}` (which `ζ ↦ ζ/ω` maps onto the punctured unit disc), is continuous there, lies in `H0 a h` there and satisfies `(E (ζ/ω)).2.1 = u₀ + ζᵏ` there.

Proof: `(ζ/ω)ᵏ = ζᵏ/ωᵏ = ζᵏ/κ`, so `u₀ + κ (ζ/ω)ᵏ = u₀ + ζᵏ`; `‖ζ/ω‖ = ‖ζ‖/‖ω‖ ∈ (0,1)` whenever `0 < ‖ζ‖ < ‖ω‖`; and continuity is `ContinuousOn.comp` with the continuous map `ζ ↦ ζ/ω` (respecting the set condition `∀ ζ ∈ {ζ | 0 < ‖ζ‖ ∧ ‖ζ‖ < ‖ω‖}, ζ/ω ∈ Metric.ball 0 1 \ {0}`). -/
theorem isChartData_normalized {a : ℝ} {h : ℂ → ℂ} {E : ℂ → ChainData} {u₀ κ : ℂ} {k : ℕ}
    (hE : IsChartData a h E u₀ κ k) {ω : ℂ} (hω : ω ^ k = κ) :
    (∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < ‖ω‖ → E (ζ / ω) ∈ H0 a h ∧ (E (ζ / ω)).2.1 = u₀ + ζ ^ k) ∧
      ContinuousOn (fun ζ : ℂ => E (ζ / ω)) {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < ‖ω‖} := by
  obtain ⟨hk, hκ, hmem, -, hcont⟩ := hE
  have hωne : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.pos_iff_ne_zero.mp hk), eq_comm] at hω
    exact hκ hω
  have hωpos : 0 < ‖ω‖ := norm_pos_iff.mpr hωne
  have hmap : ∀ ζ ∈ {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < ‖ω‖},
      ζ / ω ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro ζ hζ
    obtain ⟨hζ0, hζlt⟩ := hζ
    have hz : ζ ≠ 0 := norm_pos_iff.mp hζ0
    exact ⟨by rw [Metric.mem_ball, dist_zero_right, norm_div, div_lt_one hωpos]; exact hζlt,
      by simp [div_ne_zero hz hωne]⟩
  refine ⟨?_, ?_⟩
  · intro ζ hζ0 hζlt
    have hm := hmem (ζ / ω) (hmap ζ ⟨hζ0, hζlt⟩)
    refine ⟨hm.1, ?_⟩
    rw [hm.2, div_pow, hω]
    field_simp
  · exact hcont.comp (continuousOn_id.div_const ω) hmap

end Work.EQ
