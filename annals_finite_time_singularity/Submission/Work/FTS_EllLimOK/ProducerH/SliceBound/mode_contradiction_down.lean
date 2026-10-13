import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

set_option linter.unusedVariables false

namespace Work.FTS_EllLimOK.ProducerH.SliceBound

theorem mode_contradiction_down {V : ℝ → ℝ} {M Z₀ θ₀ : ℝ}
    (hM : 0 ≤ M) (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2)) (hZ₀ : Z₀ < 0)
    (hanti : ∀ θ ∈ Set.Ioo 0 (π / 2), θ₀ ≤ θ →
      3 * V θ * Real.cos θ + M * (Real.cos θ) ^ 3 ≤ Z₀)
    (hfl : ∀ θ ∈ Set.Ioo 0 (π / 2), -M - 2 * M * (Real.cos θ) ^ 2 ≤ V θ) :
    False := by
  have hlt : θ₀ < π / 2 := hθ₀.2
  -- Pointwise bound on the half-open interval `[θ₀, π/2) ∩ (0, π/2)`.
  have hbound : ∀ θ ∈ Set.Ioo 0 (π / 2), θ₀ ≤ θ →
      -3 * M * Real.cos θ - 5 * M * (Real.cos θ) ^ 3 ≤ Z₀ := by
    intro θ hθ hθ0
    have hcpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have h1 : 3 * (-M - 2 * M * (Real.cos θ) ^ 2) * Real.cos θ
        ≤ 3 * V θ * Real.cos θ := by
      have h3 : (0 : ℝ) ≤ 3 * Real.cos θ := by linarith
      have hmul := mul_le_mul_of_nonneg_right (hfl θ hθ) h3
      nlinarith [hmul]
    have h2 := hanti θ hθ hθ0
    nlinarith [h1, h2]
  -- The auxiliary function tends to `0` at the right endpoint.
  have hcont : Continuous fun θ : ℝ => -3 * M * Real.cos θ - 5 * M * (Real.cos θ) ^ 3 := by
    fun_prop
  have hne : (𝓝[Set.Ioo θ₀ (π / 2)] (π / 2)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt hlt)]
    exact ⟨le_of_lt hlt, le_refl _⟩
  have hlim : Filter.Tendsto (fun θ : ℝ => -3 * M * Real.cos θ - 5 * M * (Real.cos θ) ^ 3)
      (𝓝[Set.Ioo θ₀ (π / 2)] (π / 2)) (𝓝 0) := by
    have h := (hcont.tendsto (π / 2)).mono_left
      (nhdsWithin_le_nhds (a := π / 2) (s := Set.Ioo θ₀ (π / 2)))
    simpa [Real.cos_pi_div_two] using h
  have hev : ∀ᶠ θ in 𝓝[Set.Ioo θ₀ (π / 2)] (π / 2),
      -3 * M * Real.cos θ - 5 * M * (Real.cos θ) ^ 3 ≤ Z₀ := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact hbound θ ⟨by linarith [hθ.1, hθ₀.1], hθ.2⟩ (le_of_lt hθ.1)
  have h0 : (0 : ℝ) ≤ Z₀ := le_of_tendsto (hx := hne) hlim hev
  linarith [hZ₀]

end Work.FTS_EllLimOK.ProducerH.SliceBound
