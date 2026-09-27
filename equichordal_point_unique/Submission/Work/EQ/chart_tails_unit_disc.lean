import Mathlib
import Submission.Work.EQ.chart_uniform_tails_lim
import Submission.Work.EQ.chart_reparam

/-! # A chart whose principal tails are uniform on the whole punctured unit disc

`Work.EQ.chart_uniform_tails_lim` produces uniform principal tails on a *small* punctured disc; the
window dichotomy `Work.EQ.genuine_chart_window_degenerate` is stated for the punctured unit disc.
Reparametrising by a small dilation (`Work.EQ.chart_reparam`, which preserves being a punctured
chart, genuineness and the `ψ₂`-limit) bridges the two. -/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

/-- **Tails uniform on the punctured unit disc.**  Every punctured chart with a finite `ψ₂`-limit
can be reparametrised so that its principal tails are uniform on the whole punctured unit disc. -/
theorem chart_tails_unit_disc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u₀ v₀ : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u₀ k)
    (hv : Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀))
    (hgen : ¬ ∃ q ∈ H0 a h, Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) :
    ∃ (E : ℂ → ChainData) (N : ℕ), IsPuncturedChart a h E u₀ k ∧
      (¬ ∃ q ∈ H0 a h,
        Filter.Tendsto E (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) ∧
      Filter.Tendsto (fun ζ : ℂ => (E ζ).2.2)
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀) ∧
      ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 → ∀ n : ℕ, N ≤ n →
        (E ζ).1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * (E ζ).2.1) ∧
        (E ζ).1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * (E ζ).2.2) := by
  obtain ⟨δ, hδ0, hδ1, N, hN⟩ := chart_uniform_tails_lim ha0 ha1 hh he hv
  set c : ℂ := ((δ / 2 : ℝ) : ℂ) with hcdef
  have hcne : c ≠ 0 := by
    have hpos : (0 : ℝ) < δ / 2 := by linarith
    have h2 : ((δ / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
    simpa [hcdef] using h2
  have hcnorm : ‖c‖ ≤ 1 := by
    have h2 : ‖((δ / 2 : ℝ) : ℂ)‖ = δ / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
    rw [show c = ((δ / 2 : ℝ) : ℂ) from rfl, h2]
    linarith
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
  refine ⟨fun ζ => e (c * ζ), N, isPuncturedChart_comp_mul hcne hcnorm he,
    chart_comp_mul_genuine hcne hgen, chart_comp_mul_psi2 hcne hv, ?_⟩
  intro ζ hζ0 hζ1 n hn
  have hpos : (0 : ℝ) < δ / 2 := by linarith
  have hcnorm' : ‖c‖ ≤ δ / 2 := by
    rw [show c = ((δ / 2 : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos]
  have hkey : c * ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    rw [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
    refine ⟨?_, mul_ne_zero hcne (by simpa using hζ0.ne')⟩
    calc ‖c * ζ‖ = ‖c‖ * ‖ζ‖ := norm_mul _ _
      _ ≤ 1 * ‖ζ‖ := mul_le_mul_of_nonneg_right hcnorm (norm_nonneg ζ)
      _ < 1 * 1 := mul_lt_mul_of_pos_left hζ1 one_pos
      _ = 1 := one_mul 1
  have hlt : ‖c * ζ‖ < δ := by
    calc ‖c * ζ‖ = ‖c‖ * ‖ζ‖ := norm_mul _ _
      _ ≤ (δ / 2) * ‖ζ‖ := mul_le_mul_of_nonneg_right hcnorm' (norm_nonneg ζ)
      _ < (δ / 2) * 1 := mul_lt_mul_of_pos_left hζ1 hpos
      _ = δ / 2 := mul_one _
      _ < δ := by linarith
  have h0 : 0 < ‖c * ζ‖ := norm_pos_iff.mpr (mul_ne_zero hcne (by simpa using hζ0.ne'))
  have h := hN (c * ζ) h0 hlt
  exact ⟨h.1 n hn, h.2 n hn⟩

end

end Work.EQ
