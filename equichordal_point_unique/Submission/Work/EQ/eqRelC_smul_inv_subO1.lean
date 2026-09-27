import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra

namespace Work.EQ

/-- **The two branches of the relation, in closed form.**  If `ρ ^ 2 = bsq (subO1 a Q) ≠ 0`
then both `ρ⁻¹ • (subO1 a Q) - Q` and its negative satisfy `EqRelC · Q`. -/
theorem eqRelC_smul_inv_subO1 {a : ℝ} {Q : ℂ × ℂ} {ρ : ℂ}
    (hρne : ρ ≠ 0) (hρ : ρ ^ 2 = bsq (subO1 a Q)) :
    EqRelC a ((ρ⁻¹) • subO1 a Q - Q) Q ∧ EqRelC a (-((ρ⁻¹) • subO1 a Q) - Q) Q := by
  -- The common `P + Q` of the first branch is `ρ⁻¹ • (Q - O₁)`, a unit vector of the
  -- bilinear form which is parallel to `Q - O₁`; the reverse form of the relation applies.
  have hsq : bsq ((ρ⁻¹) • subO1 a Q) = 1 := by
    rw [bsq_smul, ← hρ, ← mul_pow, inv_mul_cancel₀ hρne, one_pow]
  have hpar : par ((ρ⁻¹) • subO1 a Q) (subO1 a Q) := by
    simpa using par_smul_smul (ρ⁻¹) (1 : ℂ) (subO1 a Q)
  -- The second branch is the same with the sign reversed.
  have hneg : (-((ρ⁻¹) • subO1 a Q)) = (-1 : ℂ) • ((ρ⁻¹) • subO1 a Q) := by
    rw [neg_smul, one_smul]
  have hsq2 : bsq (-((ρ⁻¹) • subO1 a Q)) = 1 := by
    rw [hneg, bsq_smul, hsq]; ring
  have hpar2 : par (-((ρ⁻¹) • subO1 a Q)) (subO1 a Q) := by
    rw [hneg]
    simpa using par_smul_smul (-1 : ℂ) (ρ⁻¹) (subO1 a Q)
  constructor
  · rw [eqRelC_iff_reverse]
    exact ⟨by rw [sub_add_cancel]; exact hsq, by rw [sub_add_cancel]; exact hpar⟩
  · rw [eqRelC_iff_reverse]
    exact ⟨by rw [sub_add_cancel]; exact hsq2, by rw [sub_add_cancel]; exact hpar2⟩

end Work.EQ
