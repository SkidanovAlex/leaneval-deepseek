import Mathlib
import Submission.Work.KMTAreas.A5.Setup

namespace Work.KMTAreas.A5

open scoped ENNReal NNReal BigOperators

/-- **Existence of the interpolation parameters `θ, V₁, V₂, V₃` (general form).**

Given `a, b ∈ (0,1)` (these will be `1/x₁`, `1/x₂`), there are `θ ∈ (0,1)` and
`V₁, V₂ > 1`, `V₃ > 0` such that

* `1/V₁ = (a - (1-θ)/2)/θ`, `1/V₂ = (b - (1-θ)/2)/θ`, `1/V₃ = (a + b - (1-θ))/θ`;
* equivalently `a`, `b` and `a+b` are the convex combinations
  `(1-θ)/2 + θ/V₁`, `(1-θ)/2 + θ/V₂` and `(1-θ) + θ/V₃`;
* `1/V₃ = 1/V₁ + 1/V₂`, i.e. `V₃` is the *harmonic* combination of `V₁` and `V₂`;
* `θ (V₃ - 1) = V₃ (1 - (a+b))`.

The construction is explicit: with `m = min (min a b) (min (1-a) (1-b))`, take
`ε = m/2`, `θ = 1 - ε` and `Vᵢ` as above.  Then `ε ≤ a/2` gives the positivity of the
numerators `a - ε/2`, `b - ε/2`, `a + b - ε` and `ε ≤ (1-a)/2` gives `a - ε/2 < θ`;
symmetrically for `b`.  Note that the constraint `a + b ≤ 1` is not needed. -/
theorem thetaSetup_aux (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hab : a + b ≤ 1) :
    ∃ (θ V₁ V₂ V₃ : ℝ), 0 < θ ∧ θ < 1 ∧ 1 < V₁ ∧ 1 < V₂ ∧ 0 < V₃ ∧
      1 / V₁ = (a - (1 - θ) / 2) / θ ∧ 1 / V₂ = (b - (1 - θ) / 2) / θ ∧
      1 / V₃ = (a + b - (1 - θ)) / θ ∧
      1 / V₃ = 1 / V₁ + 1 / V₂ ∧
      a = (1 - θ) / 2 + θ / V₁ ∧ b = (1 - θ) / 2 + θ / V₂ ∧
      a + b = (1 - θ) + θ / V₃ ∧
      θ * (V₃ - 1) = V₃ * (1 - (a + b)) := by
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  set m : ℝ := min (min a b) (min (1 - a) (1 - b)) with hm
  have hm_pos : 0 < m := by rw [hm]; exact lt_min (lt_min ha0 hb0) (lt_min h1a h1b)
  have hm_le_a : m ≤ a := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hm_le_b : m ≤ b := by rw [hm]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hm_le_1a : m ≤ 1 - a := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm_le_1b : m ≤ 1 - b := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  set ε : ℝ := m / 2 with hε
  have hε_pos : 0 < ε := by rw [hε]; linarith
  have hε_le_a : ε ≤ a / 2 := by rw [hε]; linarith
  have hε_le_b : ε ≤ b / 2 := by rw [hε]; linarith
  have hε_le_1a : ε ≤ (1 - a) / 2 := by rw [hε]; linarith
  have hε_le_1b : ε ≤ (1 - b) / 2 := by rw [hε]; linarith
  have hε_lt_one : ε < 1 := by linarith [hε_le_a, ha1]
  set θ : ℝ := 1 - ε with hθ
  have hθ_pos : 0 < θ := by rw [hθ]; linarith
  have hθ_lt_one : θ < 1 := by rw [hθ]; linarith
  have h1θ : 1 - θ = ε := by rw [hθ]; ring
  have hd1 : 0 < a - (1 - θ) / 2 := by rw [h1θ]; linarith [hε_le_a, ha0]
  have hd2 : 0 < b - (1 - θ) / 2 := by rw [h1θ]; linarith [hε_le_b, hb0]
  have hd3 : 0 < a + b - (1 - θ) := by rw [h1θ]; linarith [hε_le_a, ha0, hb0]
  have hθ_ne : θ ≠ 0 := ne_of_gt hθ_pos
  have hd1ne : a - (1 - θ) / 2 ≠ 0 := ne_of_gt hd1
  have hd2ne : b - (1 - θ) / 2 ≠ 0 := ne_of_gt hd2
  have hd3ne : a + b - (1 - θ) ≠ 0 := ne_of_gt hd3
  have hlt1 : a - (1 - θ) / 2 < θ := by rw [h1θ, hθ]; linarith [hε_le_1a, ha1]
  have hlt2 : b - (1 - θ) / 2 < θ := by rw [h1θ, hθ]; linarith [hε_le_1b, hb1]
  have hdl1 : θ / (θ / (a - (1 - θ) / 2)) = a - (1 - θ) / 2 := by field_simp
  have hdl2 : θ / (θ / (b - (1 - θ) / 2)) = b - (1 - θ) / 2 := by field_simp
  have hdl3 : θ / (θ / (a + b - (1 - θ))) = a + b - (1 - θ) := by field_simp
  refine ⟨θ, θ / (a - (1 - θ) / 2), θ / (b - (1 - θ) / 2), θ / (a + b - (1 - θ)),
    hθ_pos, hθ_lt_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hd1, one_mul]; exact hlt1
  · rw [lt_div_iff₀ hd2, one_mul]; exact hlt2
  · exact div_pos hθ_pos hd3
  · rw [one_div_div]
  · rw [one_div_div]
  · rw [one_div_div]
  · rw [one_div_div, one_div_div, one_div_div, ← add_div]; ring
  · rw [hdl1]; ring
  · rw [hdl2]; ring
  · rw [hdl3]; ring
  · field_simp; ring

theorem thetaSetup {x₁ x₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : 1 < x₂) (hsum : 1 / x₁ + 1 / x₂ ≤ 1) :
    ∃ (θ V₁ V₂ V₃ : ℝ), 0 < θ ∧ θ < 1 ∧ 1 < V₁ ∧ 1 < V₂ ∧ 0 < V₃ ∧
      1 / V₁ = (1 / x₁ - (1 - θ) / 2) / θ ∧ 1 / V₂ = (1 / x₂ - (1 - θ) / 2) / θ ∧
      1 / V₃ = (1 / x₁ + 1 / x₂ - (1 - θ)) / θ ∧
      1 / V₃ = 1 / V₁ + 1 / V₂ ∧
      1 / x₁ = (1 - θ) / 2 + θ / V₁ ∧ 1 / x₂ = (1 - θ) / 2 + θ / V₂ ∧
      1 / x₁ + 1 / x₂ = (1 - θ) + θ / V₃ ∧
      θ * (V₃ - 1) = V₃ * (1 - (1 / x₁ + 1 / x₂)) := by
  have hx1pos : (0 : ℝ) < x₁ := by linarith
  have hx2pos : (0 : ℝ) < x₂ := by linarith
  have ha0 : 0 < 1 / x₁ := one_div_pos.mpr hx1pos
  have ha1 : 1 / x₁ < 1 := by rw [div_lt_one hx1pos]; exact hx₁
  have hb0 : 0 < 1 / x₂ := one_div_pos.mpr hx2pos
  have hb1 : 1 / x₂ < 1 := by rw [div_lt_one hx2pos]; exact hx₂
  exact thetaSetup_aux (1 / x₁) (1 / x₂) ha0 ha1 hb0 hb1 hsum

end Work.KMTAreas.A5
