import Mathlib

namespace Work.WilE7.CoreStep

open Filter Topology

theorem isolatedZero_transfer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] ℝ) {k : ℕ} {g : ℝ → (Fin k → ℝ)}
    (h : (∀ᶠ x in 𝓝 (0 : ℝ), g x = g 0) ∨
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → g x = g 0 → x = 0) :
    (∀ᶠ v in 𝓝 (0 : E), (g ∘ L) v = (g ∘ L) 0) ∨
      ∃ δ : ℝ, 0 < δ ∧ ∀ v : E, ‖v‖ < δ → (g ∘ L) v = (g ∘ L) 0 → v = 0 := by
  rcases h with h | ⟨δ, hδ, hδ'⟩
  · -- `g` is eventually constant near `0`: pull back along the continuous `L`.
    left
    have hc : Tendsto (⇑L) (𝓝 (0 : E)) (𝓝 (L 0)) := L.continuous.tendsto 0
    have hL : Tendsto (⇑L) (𝓝 (0 : E)) (𝓝 (0 : ℝ)) := by
      rw [map_zero] at hc; exact hc
    filter_upwards [hL.eventually h] with v hv
    simpa [Function.comp_apply] using hv
  · -- `0` is isolated in the `g`-fibre over `0`: rescale using the operator norm.
    right
    refine ⟨δ / (‖(L : E →L[ℝ] ℝ)‖ + 1), by positivity, ?_⟩
    intro v hv hv0
    simp only [Function.comp_apply, map_zero] at hv0 ⊢
    have hpos : (0 : ℝ) < ‖(L : E →L[ℝ] ℝ)‖ + 1 := by positivity
    have hstep : (‖(L : E →L[ℝ] ℝ)‖ + 1) * ‖v‖ < δ := by
      have := mul_lt_mul_of_pos_left hv hpos
      rwa [mul_div_cancel₀ _ (ne_of_gt hpos)] at this
    have hLv : ‖L v‖ < δ := by
      have h1 : ‖(L : E →L[ℝ] ℝ) v‖ ≤ ‖(L : E →L[ℝ] ℝ)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ v
      have h2 : ‖(L : E →L[ℝ] ℝ)‖ * ‖v‖ ≤ (‖(L : E →L[ℝ] ℝ)‖ + 1) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v); linarith
      have h3 : ‖(L : E →L[ℝ] ℝ) v‖ = ‖L v‖ := rfl
      rw [h3] at h1
      linarith
    have hzero : L v = 0 := hδ' (L v) (by simpa using hLv) hv0
    exact L.injective (by rw [hzero, map_zero])

end Work.WilE7.CoreStep
