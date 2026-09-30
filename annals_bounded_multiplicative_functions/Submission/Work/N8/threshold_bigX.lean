import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Filter

theorem threshold_bigX (ε c δ : ℝ) (K : ℕ) (hK : 0 < K) (hε : 0 < ε) (hc : 0 < c)
    (hδ : 0 < δ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      1 ≤ X ∧ 1 ≤ Real.log X ∧ 3 ≤ X ^ (ε ^ 2 / 2) ∧
      Real.log X ≤ X ^ (ε ^ 2 / 2) ∧
      (32 / 5) * (K : ℝ) * (1 / δ + 2) * (Real.log X) ^ 2 ≤ c * X ^ (ε ^ 2 / 2) := by
  have hα : 0 < ε ^ 2 / 2 := by positivity
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have key : ∀ᶠ X : ℝ in Filter.atTop,
      1 ≤ X ∧ 1 ≤ Real.log X ∧ 3 ≤ X ^ (ε ^ 2 / 2) ∧
      Real.log X ≤ X ^ (ε ^ 2 / 2) ∧
      (32 / 5) * (K : ℝ) * (1 / δ + 2) * (Real.log X) ^ 2 ≤ c * X ^ (ε ^ 2 / 2) := by
    have h4 : ∀ᶠ X : ℝ in Filter.atTop, Real.log X ≤ X ^ (ε ^ 2 / 2) := by
      have hb := (isLittleO_log_rpow_atTop hα).bound (show (0 : ℝ) < 1 by norm_num)
      filter_upwards [hb, Filter.eventually_ge_atTop (0 : ℝ)] with X hbX hX0
      have hg : ‖X ^ (ε ^ 2 / 2)‖ = X ^ (ε ^ 2 / 2) :=
        Real.norm_of_nonneg (Real.rpow_nonneg hX0 _)
      rw [hg] at hbX
      calc Real.log X ≤ ‖Real.log X‖ := le_abs_self _
        _ ≤ 1 * X ^ (ε ^ 2 / 2) := hbX
        _ = X ^ (ε ^ 2 / 2) := one_mul _
    have h5r : ∀ᶠ X : ℝ in Filter.atTop,
        (32 / 5) * (K : ℝ) * (1 / δ + 2) * Real.log X ^ (2 : ℝ) ≤ c * X ^ (ε ^ 2 / 2) := by
      set M : ℝ := (32 / 5) * (K : ℝ) * (1 / δ + 2) with hMdef
      have hMpos : 0 < M := by
        rw [hMdef]
        have hd : (0 : ℝ) < 1 / δ + 2 := by positivity
        positivity
      have hcM : 0 < c / M := div_pos hc hMpos
      have hb := (isLittleO_log_rpow_rpow_atTop 2 hα).bound hcM
      filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with X hbX hX1
      have hX0 : (0 : ℝ) < X := by linarith
      have hxpow : (0 : ℝ) < X ^ (ε ^ 2 / 2) := Real.rpow_pos_of_pos hX0 _
      have hlog0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
      have hlogr : (0 : ℝ) ≤ Real.log X ^ (2 : ℝ) := Real.rpow_nonneg hlog0 _
      have hbX' : Real.log X ^ (2 : ℝ) ≤ (c / M) * X ^ (ε ^ 2 / 2) := by
        rw [Real.norm_of_nonneg hlogr, Real.norm_of_nonneg hxpow.le] at hbX
        exact hbX
      calc M * Real.log X ^ (2 : ℝ) ≤ M * ((c / M) * X ^ (ε ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_left hbX' hMpos.le
        _ = c * X ^ (ε ^ 2 / 2) := by rw [← mul_assoc, mul_div_cancel₀ c hMpos.ne']
    have h5 : ∀ᶠ X : ℝ in Filter.atTop,
        (32 / 5) * (K : ℝ) * (1 / δ + 2) * (Real.log X) ^ 2 ≤ c * X ^ (ε ^ 2 / 2) := by
      filter_upwards [h5r] with X hX
      simpa only [Real.rpow_ofNat] using hX
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      (tendsto_rpow_atTop hα).eventually_ge_atTop 3, h4, h5] with X h1 h2 h3 h4' h5'
    exact ⟨h1, h2, h3, h4', h5'⟩
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp key
  exact ⟨X₀, hX₀⟩

end Work.N8
