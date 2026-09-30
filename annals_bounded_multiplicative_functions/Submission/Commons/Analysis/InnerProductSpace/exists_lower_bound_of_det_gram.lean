import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.InnerProductSpace

open Matrix

/-- If the Gram determinant of a family `s` of vectors in `EuclideanSpace ℝ (Fin l)` is bounded
below by a positive constant `c`, then the linear map `w ↦ ∑ i, w i • s i` is bounded below: there
is a positive `c'` with `c' * ‖w‖ ≤ ‖∑ i, w i • s i‖` for every `w`. -/
theorem exists_lower_bound_of_det_gram {l : ℕ} (s : Fin l → EuclideanSpace ℝ (Fin l))
    {c A : ℝ} (hc : 0 < c) (hA : 0 < A) (hsi : ∀ i, ‖s i‖ ≤ A)
    (h : c ≤ (Matrix.gram ℝ s).det) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ w : Fin l → ℝ, c' * ‖w‖ ≤ ‖∑ i : Fin l, w i • s i‖ := by
  -- The Gram determinant is positive, hence `s` is linearly independent.
  have hdet : (Matrix.gram ℝ s).det ≠ 0 := ne_of_gt (lt_of_lt_of_le hc h)
  have hli : LinearIndependent ℝ s := Matrix.linearIndependent_of_det_gram_ne_zero hdet
  -- The linear combination map `w ↦ ∑ i, w i • s i` is injective.
  have hinj : Function.Injective (Fintype.linearCombination ℝ s) :=
    LinearIndependent.fintypeLinearCombination_injective hli
  have hker : LinearMap.ker (Fintype.linearCombination ℝ s) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  -- An injective linear map on a finite dimensional space is antilipschitz, hence bounded below.
  obtain ⟨K, _hKpos, hK⟩ :=
    LinearMap.exists_antilipschitzWith (Fintype.linearCombination ℝ s) hker
  obtain ⟨c', hc'pos, hc'⟩ :=
    (antilipschitzWith_iff_exists_mul_le_norm
      (f := Fintype.linearCombination ℝ s)).mp ⟨K, hK⟩
  refine ⟨c', hc'pos, fun w => ?_⟩
  simpa only [Fintype.linearCombination_apply] using hc' w

end Commons.Analysis.InnerProductSpace