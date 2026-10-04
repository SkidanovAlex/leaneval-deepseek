import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

/-- The quadratic form `∑ᵢ ∑ⱼ Aᵢⱼ vᵢ vⱼ` is the dot product of `v` with `A *ᵥ v`. -/
lemma sum_sum_mul_eq_dotProduct_quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ i, ∑ j, A i j * v i * v j = dotProduct v (A.mulVec v) := by
  rw [Matrix.dot_mulVec_eq_sum_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A nonzero vector has positive sum of squares. -/
lemma sum_sq_pos_of_ne_zero {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < ∑ i, (v i) ^ 2 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hk' : v k ≠ 0 := by simpa using hk
  have hpos := Finset.sum_pos' (s := Finset.univ) (fun i _ => sq_nonneg (v i))
    ⟨k, Finset.mem_univ k, sq_pos_of_ne_zero hk'⟩
  simpa using hpos

/-- A square real matrix whose associated quadratic form dominates `lam * ‖·‖²` with `lam > 0`
is nonsingular. -/
theorem det_ne_zero_of_quadForm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, A i j * v i * v j) :
    A.det ≠ 0 := by
  intro hdet
  -- a singular matrix has a nonzero kernel vector
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  -- for such a vector the quadratic form vanishes ...
  have h0 : ∑ i, ∑ j, A i j * v i * v j = 0 := by
    rw [sum_sum_mul_eq_dotProduct_quadForm, hv, dotProduct_zero]
  -- ... but `lam * ∑ᵢ vᵢ²` is strictly positive
  have hvpos : 0 < ∑ i, (v i) ^ 2 := sum_sq_pos_of_ne_zero hvne
  have hle := h v
  rw [h0] at hle
  have hpos := mul_pos hlam hvpos
  linarith

end Work.Diff.STE.flat
