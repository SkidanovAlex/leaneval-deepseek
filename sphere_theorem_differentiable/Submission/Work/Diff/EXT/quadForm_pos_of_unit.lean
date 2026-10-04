import Mathlib
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- A quadratic form on `ℝⁿ` given by a (not necessarily symmetric) matrix is homogeneous of
degree two: `Q (c • v) = c² * Q v`. -/
private lemma quadForm_smul {n : ℕ} (v : Fin n → ℝ) (c : ℝ) (A : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, (c • v) i * (c • v) j * A i j) = c^2 * ∑ i, ∑ j, v i * v j * A i j := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- **Positivity on the unit sphere upgrades to positive definiteness.**  If the quadratic form
`v ↦ ∑ᵢ ∑ⱼ vᵢ vⱼ W p i j` is positive on the unit sphere `‖v‖ = 1`, then it is positive on every
nonzero vector: by homogeneity of degree two it suffices to rescale `v` to unit norm. -/
theorem quadForm_pos_of_unit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W : ℝ × E → Work.Diff.EXT.MatE (E := E)} {p : ℝ × E}
    (hunit : ∀ v : Fin (Module.finrank ℝ E) → ℝ, ‖v‖ = 1 →
        0 < ∑ i, ∑ j, v i * v j * W p i j) :
    ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
        0 < ∑ i, ∑ j, v i * v j * W p i j := by
  intro v hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hne : ‖v‖ ≠ 0 := ne_of_gt hnorm
  set c : ℝ := (‖v‖)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr hnorm
  have hunit_v : ‖c • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc, inv_mul_cancel₀ hne]
  have hQ := hunit (c • v) hunit_v
  rw [quadForm_smul v c (W p)] at hQ
  exact pos_of_mul_pos_right hQ (le_of_lt (pow_pos hcpos 2))

end Work.Diff.EXT
