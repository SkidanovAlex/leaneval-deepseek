import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

/-- Jordan's inequality for `cos`: for `|θ| ≤ π/2`, `1 - (2/π)|θ| ≤ cos θ`.
Obtained from Mathlib's one-sided forms by putting both cases on the side of `θ ≥ 0`. -/
lemma one_sub_mul_abs_le_cos {θ : ℝ} (hθ : |θ| ≤ Real.pi / 2) :
    1 - 2 / Real.pi * |θ| ≤ Real.cos θ := by
  rcases le_total 0 θ with h | h
  · have h' : θ ≤ Real.pi / 2 := by rwa [abs_of_nonneg h] at hθ
    have hc := Real.one_sub_mul_le_cos (x := θ) h h'
    rwa [abs_of_nonneg h]
  · have h' : -(Real.pi / 2) ≤ θ := by rw [abs_of_nonpos h] at hθ; linarith
    have hc := Real.one_add_mul_le_cos (x := θ) h' h
    rw [abs_of_nonpos h]
    linarith

/-- A form of Jordan's inequality: on `[-π/2, π/2]`, `cos` lies above the chord joining
`(-π/2, 0)` to `(0, 1)`, i.e. `π/2 - |θ| ≤ (π/2) cos θ`. -/
theorem pi_div_two_sub_abs_le_cos {θ : ℝ} (hθ : |θ| ≤ Real.pi / 2) :
    Real.pi / 2 - |θ| ≤ Real.pi / 2 * Real.cos θ := by
  have h := one_sub_mul_abs_le_cos hθ
  have h2 : Real.pi / 2 * (1 - 2 / Real.pi * |θ|) ≤ Real.pi / 2 * Real.cos θ :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have heq : Real.pi / 2 * (1 - 2 / Real.pi * |θ|) = Real.pi / 2 - |θ| := by
    field_simp
  rwa [heq] at h2

end Work.FTS.BSIdent.Cyl.DecayAux
