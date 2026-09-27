import Mathlib

/-!
# Existence of an orthonormal frame adapted to a normal vector in `ℝ³`

Given two linearly independent vectors `V1 V2 : Fin 3 → ℝ` (i.e. a `2`-plane in `ℝ³`),
we produce a unit vector `u` orthogonal to both `V1` and `V2` (their normal), together
with vectors `e1 e2` so that `e1, e2, u` form an orthonormal family (in the standard
Euclidean dot product `∑ i, x i * y i`).

The construction is completely explicit:
* `U := V1 ⨯₃ V2` is a non-zero normal vector (cross product),
* `u := (√(U ⬝ᵥ U))⁻¹ • U` is its normalisation,
* `e1 := (√(V1 ⬝ᵥ V1))⁻¹ • V1` normalises `V1` (which is automatically orthogonal to `u`),
* `e2 := u ⨯₃ e1` is the cross product of the two unit vectors `u, e1`, hence again a unit
  vector orthogonal to both.

All the orthogonality and normality identities then follow from the standard identities
of the cross product and the bilinearity of the dot product.
-/

open Matrix
open scoped Matrix

namespace Work.EKLComp

/-- The Euclidean dot product on `Fin 3 → ℝ` is positive definite. -/
lemma dotProduct_self_pos {x : Fin 3 → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  rw [dotProduct]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- Normalising a non-zero vector with respect to the Euclidean dot product yields a unit
vector. -/
lemma dotProduct_normalize_self {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) ⬝ᵥ ((Real.sqrt (x ⬝ᵥ x))⁻¹ • x) = 1 := by
  have hpos : 0 < x ⬝ᵥ x := dotProduct_self_pos hx
  set s := Real.sqrt (x ⬝ᵥ x) with hs
  have hs0 : s ≠ 0 := by rw [hs]; exact ne_of_gt (Real.sqrt_pos_of_pos hpos)
  have hsq : s ^ 2 = x ⬝ᵥ x := by rw [hs, Real.sq_sqrt (le_of_lt hpos)]
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [← hsq]
  field_simp

theorem exists_euclid_orthonormal_normal_frame (V1 V2 : Fin 3 → ℝ)
    (h : LinearIndependent ℝ ![V1, V2]) :
    ∃ e1 e2 u : Fin 3 → ℝ,
      (∑ i, e1 i * e1 i = 1) ∧ (∑ i, e2 i * e2 i = 1) ∧ (∑ i, u i * u i = 1) ∧
      (∑ i, e1 i * e2 i = 0) ∧ (∑ i, e1 i * u i = 0) ∧ (∑ i, e2 i * u i = 0) ∧
      (∑ i, u i * V1 i = 0) ∧ (∑ i, u i * V2 i = 0) := by
  set U := V1 ⨯₃ V2 with hU
  have hU0 : U ≠ 0 := by
    rw [hU]; exact crossProduct_ne_zero_iff_linearIndependent.mpr h
  have hV1 : V1 ≠ 0 := by
    have hh := h.ne_zero 0
    simpa using hh
  have hV1U : V1 ⬝ᵥ U = 0 := by rw [hU]; exact dot_self_cross V1 V2
  have hV2U : V2 ⬝ᵥ U = 0 := by rw [hU]; exact dot_cross_self V1 V2
  have hUV1 : U ⬝ᵥ V1 = 0 := by rw [dotProduct_comm]; exact hV1U
  have hUV2 : U ⬝ᵥ V2 = 0 := by rw [dotProduct_comm]; exact hV2U
  set s := Real.sqrt (V1 ⬝ᵥ V1) with hs
  set t := Real.sqrt (U ⬝ᵥ U) with ht
  have h1 : (s⁻¹ • V1) ⬝ᵥ (s⁻¹ • V1) = 1 := by simpa [hs] using dotProduct_normalize_self hV1
  have h2 : (t⁻¹ • U) ⬝ᵥ (t⁻¹ • U) = 1 := by simpa [ht] using dotProduct_normalize_self hU0
  have h5 : (s⁻¹ • V1) ⬝ᵥ (t⁻¹ • U) = 0 := by
    rw [smul_dotProduct, dotProduct_smul, hV1U, smul_zero, smul_zero]
  have h5' : (t⁻¹ • U) ⬝ᵥ (s⁻¹ • V1) = 0 := by rw [dotProduct_comm]; exact h5
  refine ⟨s⁻¹ • V1, (t⁻¹ • U) ⨯₃ (s⁻¹ • V1), t⁻¹ • U, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (s⁻¹ • V1) ⬝ᵥ (s⁻¹ • V1) = 1
    exact h1
  · show ((t⁻¹ • U) ⨯₃ (s⁻¹ • V1)) ⬝ᵥ ((t⁻¹ • U) ⨯₃ (s⁻¹ • V1)) = 1
    rw [cross_dot_cross, h2, h1, h5', h5]
    ring
  · show (t⁻¹ • U) ⬝ᵥ (t⁻¹ • U) = 1
    exact h2
  · show (s⁻¹ • V1) ⬝ᵥ ((t⁻¹ • U) ⨯₃ (s⁻¹ • V1)) = 0
    exact dot_cross_self (t⁻¹ • U) (s⁻¹ • V1)
  · show (s⁻¹ • V1) ⬝ᵥ (t⁻¹ • U) = 0
    exact h5
  · show ((t⁻¹ • U) ⨯₃ (s⁻¹ • V1)) ⬝ᵥ (t⁻¹ • U) = 0
    rw [dotProduct_comm]; exact dot_self_cross (t⁻¹ • U) (s⁻¹ • V1)
  · show (t⁻¹ • U) ⬝ᵥ V1 = 0
    rw [smul_dotProduct, hUV1, smul_zero]
  · show (t⁻¹ • U) ⬝ᵥ V2 = 0
    rw [smul_dotProduct, hUV2, smul_zero]

end Work.EKLComp
