import Mathlib
import Submission.Work.FIArea3.JointCount.angSector

namespace Work.FIArea3.JointCount

set_option linter.unusedVariables false

/-- For `z` in the angular sector `{a < ‖z‖ ∧ ‖z‖ ≤ b ∧ arg z ∈ (α, β]}` whose angular width
`β - α` is at most `π`, the projection of `z` onto the bisector direction `(cos m, sin m)`,
`m = (α + β)/2`, is at least `a * cos((β - α)/2)`.

Writing `z = ‖z‖ (cos θ + i sin θ)` with `θ = arg z`, the projection equals
`‖z‖ cos(θ - m)`, and `|θ - m| ≤ (β - α)/2 ≤ π/2`, so `cos(θ - m) ≥ cos((β - α)/2) ≥ 0`;
multiplying by `a < ‖z‖` gives the claim. -/
theorem angSector_proj_ge (a b α β : ℝ) (ha : 0 < a) (hab : a ≤ b) (hαβ : α ≤ β)
    (hℓ : β - α ≤ Real.pi) (z : ℂ) (hz : z ∈ angSector a b (Set.Ioc α β)) :
    a * Real.cos ((β - α) / 2)
      ≤ z.re * Real.cos ((α + β) / 2) + z.im * Real.sin ((α + β) / 2) := by
  obtain ⟨hza, _hzb, hzarg⟩ := hz
  obtain ⟨hαθ, hθβ⟩ := hzarg
  set θ := z.arg with hθ
  set δ := (β - α) / 2 with hδ
  set m := (α + β) / 2 with hm
  have hδpi2 : δ ≤ Real.pi / 2 := by rw [hδ]; linarith
  have hδpi : δ ≤ Real.pi := le_trans hδpi2 (by linarith [Real.pi_pos])
  have hδnn : 0 ≤ δ := by rw [hδ]; linarith
  have hcosδnn : 0 ≤ Real.cos δ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hδpi2
  have hθm_ub : θ - m ≤ δ := by rw [hθ, hm, hδ]; linarith
  have hθm_lb : -(δ) ≤ θ - m := by rw [hθ, hm, hδ]; linarith
  have habs : |θ - m| ≤ δ := abs_le.mpr ⟨hθm_lb, hθm_ub⟩
  have hcos_ge : Real.cos δ ≤ Real.cos (θ - m) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (θ - m)) hδpi habs
    rwa [Real.cos_abs] at h
  have hEq : z.re * Real.cos m + z.im * Real.sin m = ‖z‖ * Real.cos (θ - m) := by
    rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z, hθ, Real.cos_sub]
    ring
  rw [hEq]
  calc a * Real.cos δ ≤ ‖z‖ * Real.cos δ := mul_le_mul_of_nonneg_right hza.le hcosδnn
    _ ≤ ‖z‖ * Real.cos (θ - m) := mul_le_mul_of_nonneg_left hcos_ge (norm_nonneg z)

end Work.FIArea3.JointCount
