import Mathlib

namespace Work.Whitney

/-- Given two linear maps `A B : ℝⁿ → ℝ^{2n}` whose ranges span the whole target,
the map `(x, y) ↦ A x + B y` is a continuous linear equivalence
`ℝⁿ × ℝⁿ ≃L[ℝ] ℝ^{2n}`, and its inverse recovers `x` from `A x` and `y` from `B y`. -/
theorem coprod_equiv_of_range_sup {n : ℕ}
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
    (h : A.range ⊔ B.range = ⊤) :
    ∃ T : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (2 * n)),
      (∀ x y, T (x, y) = A x + B y) ∧
      (∀ x, T.symm (A x) = (x, 0)) ∧
      (∀ y, T.symm (B y) = (0, y)) := by
  let f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) := A.coprod B
  have hrange : f.range = ⊤ := by
    rw [ContinuousLinearMap.range_coprod]
    exact h
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace]
    simp [Fintype.card_fin]
    ring
  have hker : f.ker = ⊥ := by
    have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hrange
    have hinj : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr hsurj
    exact LinearMap.ker_eq_bot.mpr hinj
  let T : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) := ContinuousLinearEquiv.ofBijective f hker hrange
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x y
    show f (x, y) = A x + B y
    simp [f]
  · intro x
    have hx : T (x, 0) = A x := by
      show f (x, 0) = A x
      simp [f]
    rw [← hx, T.symm_apply_apply]
  · intro y
    have hy : T (0, y) = B y := by
      show f (0, y) = B y
      simp [f]
    rw [← hy, T.symm_apply_apply]

end Work.Whitney
