import Submission.Work.ThomBordism.PontryaginThom.Orthogonal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `orthProj` depends only on the plane

`Orthogonal.lean` defines `orthProj A = A (AᵀA)⁻¹ Aᵀ` — the orthogonal projection onto the plane
spanned by the frame `A` — and `orthInj A = 1 - orthProj A`, the insertion of the orthogonal
complement.  The complement construction of the normal bundle (`ComplementBundle.lean`) needs the
complement to be *chart-independent*: the insertion `I_S = orthInj A ∘ complInj S` (with `S` the
chart index of the Grassmannian, `Complement.lean`) must satisfy
`I_S (P_S u) = I_T (P_T u)` for two chart indices `S`, `T` of the *same* plane (`Pi_agree` of
`Splitting.lean`).  Since `orthInj` depends on the frame only through its plane, this is the fact
that `orthProj` — and hence `orthInj` — *depends only on the plane*:

* `range_orthProj_eq` — the range of `orthProj A` is the plane `range (coeffMap A)`;
* `orthProj_eq_of_range_coeffMap` — **two frames spanning the same plane have the same orthogonal
  projection**.

The proof of the second is the standard uniqueness of the orthogonal projection: both `orthProj A`
and `orthProj B` fix their common range `R` and are self-adjoint
(`dotProduct_orthProj_comm`), so with `y = P x - Q x` one has `P y = Q y = y` and hence
`⟪y, y⟫ = ⟪y, P x⟫ - ⟪y, Q x⟫ = ⟪P y, x⟫ - ⟪Q y, x⟫ = 0`, which forces `y = 0` by positive
definiteness of the dot product (`dotProduct_self_eq_zero`).
-/

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

variable {k : ℕ}

/-! ## Positivity and adjunction for the dot product -/

/-- **Positive definiteness of the dot product on `ℝⁿ`**: `⟪w, w⟫ = 0` forces `w = 0`. -/
theorem dotProduct_self_eq_zero {n : ℕ} {w : Fin n → ℝ} (h : dotProduct w w = 0) : w = 0 := by
  funext i
  have hsum : ∑ j : Fin n, w j * w j = 0 := by simpa [dotProduct] using h
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w j * w j := fun j _ => mul_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))

/-- The adjunction between `mulVec` and the dot product, in a notation-free form. -/
theorem dotProduct_mulVec_sq {n : ℕ} (a : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) :
    dotProduct a (M.mulVec b) = dotProduct ((Matrix.transpose M).mulVec a) b := by
  have h1 : dotProduct a (M.mulVec b) = dotProduct (Matrix.vecMul a M) b :=
    Matrix.dotProduct_mulVec a M b
  have h2 : Matrix.vecMul a M = (Matrix.transpose M).mulVec a :=
    (Matrix.mulVec_transpose M a).symm
  rw [h1, h2]

/-- `orthProj` evaluated by `mulVec` of its matrix. -/
theorem orthProj_mulVec (A : Fin 8 → Euc (8 + k)) (b : Fin (8 + k) → ℝ) :
    orthProj A b = (orthMat A).mulVec b := rfl

/-- **The orthogonal projection is self-adjoint** for the standard dot product. -/
theorem dotProduct_orthProj_comm (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A)
    (a b : Fin (8 + k) → ℝ) :
    dotProduct a (orthProj A b) = dotProduct (orthProj A a) b := by
  rw [orthProj_mulVec, orthProj_mulVec, dotProduct_mulVec_sq a (orthMat A) b,
    orthMat_transpose A hA]

/-! ## The range of the orthogonal projection, and dependence on the plane only -/

/-- The range of the orthogonal projection onto the plane of `A` is that plane. -/
theorem range_orthProj_eq (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A) :
    LinearMap.range (orthProj A) = LinearMap.range (coeffMap A) := by
  refine le_antisymm (range_orthProj_le A) ?_
  rintro w ⟨v, rfl⟩
  exact ⟨coeffMap A v, orthProj_coeffMap A hA v⟩

/-- **The orthogonal projection depends only on the plane of the frame**: two linearly independent
frames spanning the same subspace of `ℝ^{8+k}` have the same orthogonal projection, hence the same
orthogonal insertion `orthInj`. -/
theorem orthProj_eq_of_range_coeffMap (A B : Fin 8 → Euc (8 + k))
    (hA : LinearIndependent ℝ A) (hB : LinearIndependent ℝ B)
    (h : LinearMap.range (coeffMap A) = LinearMap.range (coeffMap B)) :
    orthProj A = orthProj B := by
  have hRA : LinearMap.range (orthProj A) = LinearMap.range (coeffMap A) := range_orthProj_eq A hA
  have hRB : LinearMap.range (orthProj B) = LinearMap.range (coeffMap B) := range_orthProj_eq B hB
  have hPfix : ∀ u ∈ LinearMap.range (coeffMap A), orthProj A u = u := fun u hu => by
    obtain ⟨v, rfl⟩ := hu
    exact orthProj_coeffMap A hA v
  have hQfix : ∀ u ∈ LinearMap.range (coeffMap B), orthProj B u = u := fun u hu => by
    obtain ⟨v, rfl⟩ := hu
    exact orthProj_coeffMap B hB v
  refine LinearMap.ext fun x => ?_
  set y : Fin (8 + k) → ℝ := orthProj A x - orthProj B x with hy
  have hPy : orthProj A y = y := by
    rw [hy, map_sub]
    congr 1
    · exact hPfix _ (range_orthProj_le A ⟨x, rfl⟩)
    · exact hPfix _ (by rw [h]; exact range_orthProj_le B ⟨x, rfl⟩)
  have hQy : orthProj B y = y := by
    rw [hy, map_sub]
    congr 1
    · exact hQfix _ (by rw [← h]; exact range_orthProj_le A ⟨x, rfl⟩)
    · exact hQfix _ (range_orthProj_le B ⟨x, rfl⟩)
  have hlin : dotProduct y y
      = dotProduct y (orthProj A x) - dotProduct y (orthProj B x) := by
    rw [hy]
    simp only [dotProduct, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hA2 : dotProduct y (orthProj A x) = dotProduct y x := by
    rw [dotProduct_orthProj_comm A hA y x, hPy]
  have hB2 : dotProduct y (orthProj B x) = dotProduct y x := by
    rw [dotProduct_orthProj_comm B hB y x, hQy]
  have hz : dotProduct y y = 0 := by rw [hlin, hA2, hB2, sub_self]
  have hy0 : y = 0 := dotProduct_self_eq_zero hz
  rw [hy] at hy0
  exact sub_eq_zero.mp hy0

end

end Work.ThomBordism.PontryaginThom
