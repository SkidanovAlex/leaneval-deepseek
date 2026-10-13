import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `π` is the scoped notation for `Real.pi`; without this line the identifier `π` is
-- unknown (the workspace sets `autoImplicit = false`), so the statement itself does
-- not elaborate.
open scoped Real

namespace Work.FTS_EllLimOK.ProducerH.SliceBound

/-- Upper mode contradiction: the two-sided pointwise bounds
`Z₀ ≤ 3 V θ cos θ - M cos³θ` (for `θ ≥ θ₀`) and `V θ ≤ M + 2M cos²θ` are incompatible
with `Z₀ > 0` when `θ₀ < π/2`, because letting `θ → π/2⁻` forces `Z₀ ≤ 0`.

Indeed, multiplying the second bound by `3 cos θ ≥ 0` and inserting it into the first
gives `Z₀ ≤ M cos θ (3 + 5 cos²θ)` for every `θ ∈ (θ₀, π/2)`; the right-hand side tends
to `0` as `θ → π/2` (continuity of `cos`), so `Z₀ ≤ 0`. -/
theorem mode_contradiction_up {V : ℝ → ℝ} {M Z₀ θ₀ : ℝ}
    (hM : 0 ≤ M) (hθ₀ : θ₀ ∈ Set.Ioo 0 (π / 2)) (hZ₀ : 0 < Z₀)
    (hmono : ∀ θ ∈ Set.Ioo 0 (π / 2), θ₀ ≤ θ →
      Z₀ ≤ 3 * V θ * Real.cos θ - M * (Real.cos θ) ^ 3)
    (hfu : ∀ θ ∈ Set.Ioo 0 (π / 2), V θ ≤ M + 2 * M * (Real.cos θ) ^ 2) :
    False := by
  -- Pointwise reduction to the single bound `Z₀ ≤ M cos θ (3 + 5 cos²θ)`.
  have key : ∀ θ ∈ Set.Ioo 0 (π / 2), θ₀ ≤ θ →
      Z₀ ≤ M * Real.cos θ * (3 + 5 * (Real.cos θ) ^ 2) := by
    intro θ hθ hge
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have h1 := hmono θ hθ hge
    have h2 := hfu θ hθ
    have h3 : 3 * V θ * Real.cos θ ≤ 3 * (M + 2 * M * (Real.cos θ) ^ 2) * Real.cos θ := by
      nlinarith [mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ 3 * Real.cos θ)]
    nlinarith [h1, h3]
  -- The right-hand side is continuous and vanishes at `π/2`.
  have hcont : Continuous (fun θ : ℝ => M * Real.cos θ * (3 + 5 * (Real.cos θ) ^ 2)) := by
    fun_prop
  have h0 : M * Real.cos (π / 2) * (3 + 5 * (Real.cos (π / 2)) ^ 2) = 0 := by
    rw [Real.cos_pi_div_two]; ring
  -- Hence it is `< Z₀` on a left-neighbourhood of `π/2`.
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp (hcont.continuousAt (x := π / 2)) Z₀ hZ₀
  -- Pick `θ = π/2 - γ` in `(θ₀, π/2)` and inside that neighbourhood.
  set γ : ℝ := min (δ / 2) ((π / 2 - θ₀) / 2) with hγdef
  have hγpos : 0 < γ := lt_min (by linarith [hδpos]) (by linarith [hθ₀.2])
  have hγle : γ ≤ (π / 2 - θ₀) / 2 := min_le_right _ _
  have hγlt : γ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith [hδpos])
  set θ : ℝ := π / 2 - γ with hθdef
  have hθmem : θ ∈ Set.Ioo 0 (π / 2) := by
    refine ⟨?_, ?_⟩
    · rw [hθdef]; linarith [hγle, hθ₀.1]
    · rw [hθdef]; linarith [hγpos]
  have hθge : θ₀ ≤ θ := by rw [hθdef]; linarith [hγle]
  have hdist : dist θ (π / 2) < δ := by
    rw [Real.dist_eq, hθdef]
    have : π / 2 - γ - π / 2 = -γ := by ring
    rw [this, abs_neg, abs_of_pos hγpos]
    exact hγlt
  have hFlt : M * Real.cos θ * (3 + 5 * (Real.cos θ) ^ 2) < Z₀ := by
    have h := hδ (x := θ) hdist
    simp only [Real.dist_eq, h0, sub_zero] at h
    exact (abs_lt.mp h).2
  linarith [key θ hθmem hθge, hFlt]

end Work.FTS_EllLimOK.ProducerH.SliceBound
