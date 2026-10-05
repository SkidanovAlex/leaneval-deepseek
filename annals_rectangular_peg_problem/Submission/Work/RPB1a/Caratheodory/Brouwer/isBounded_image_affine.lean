import Mathlib

namespace Work.RPB1a.Caratheodory.Brouwer

/-- The affine similarity `z ↦ c * z + b` of the plane is Lipschitz with constant `‖c‖`. -/
theorem lipschitzWith_mul_add (c b : ℂ) :
    LipschitzWith ‖c‖₊ (fun z : ℂ => c * z + b) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h : (c * x + b) - (c * y + b) = c * (x - y) := by ring
  rw [dist_eq_norm, dist_eq_norm, h, norm_mul]
  simp

/-- The inverse affine similarity `z ↦ c⁻¹ * (z - b)` of the plane is Lipschitz with constant
`‖c⁻¹‖`. -/
theorem lipschitzWith_inv_sub (c b : ℂ) :
    LipschitzWith ‖c⁻¹‖₊ (fun z : ℂ => c⁻¹ * (z - b)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h : c⁻¹ * (x - b) - c⁻¹ * (y - b) = c⁻¹ * (x - y) := by ring
  rw [dist_eq_norm, dist_eq_norm, h, norm_mul]
  simp

/-- **Boundedness of the image of a bounded set under the affine similarity `z ↦ c * z + b` of the
plane and under its inverse `z ↦ c⁻¹ * (z - b)`** (for `c ≠ 0`). -/
theorem isBounded_image_affine {c b : ℂ} (hc : c ≠ 0) {S : Set ℂ}
    (hS : Bornology.IsBounded S) :
    Bornology.IsBounded ((fun z : ℂ => c * z + b) '' S) ∧
      Bornology.IsBounded ((fun z : ℂ => c⁻¹ * (z - b)) '' S) := by
  constructor
  · exact (lipschitzWith_mul_add c b).isBounded_image hS
  · exact (lipschitzWith_inv_sub c b).isBounded_image hS

end Work.RPB1a.Caratheodory.Brouwer
