import Mathlib

namespace Work.Mostow

/-- The determinant of `1 + (innerSL ℝ y).smulRight x` is `1 + ⟪y, x⟫`.

This is the rank-one determinant formula `det (1 + f ⊗ x) = 1 + f x` for the
particular case where `f = innerSL ℝ y` is the (real) Riesz dual of `y`. -/
theorem det_one_add_smulRight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x y : E) :
    LinearMap.det ((1 : E →ₗ[ℝ] E) + (innerSL ℝ y : E →ₗ[ℝ] ℝ).smulRight x) = 1 + inner ℝ y x := by
  classical
  set f : E →ₗ[ℝ] ℝ := (innerSL ℝ y : E →ₗ[ℝ] ℝ) with hf
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb
  -- Matrix of the rank-one map `f.smulRight x` is the outer product `vecMulVec`.
  have hmat : LinearMap.toMatrix b b (f.smulRight x) = Matrix.vecMulVec (b.repr x) (f ∘ b) :=
    LinearMap.toMatrix_smulRight b b f x
  have hm : LinearMap.toMatrix b b (1 + f.smulRight x)
      = 1 + Matrix.vecMulVec (b.repr x) (f ∘ b) := by
    rw [(LinearMap.toMatrix b b).map_add, LinearMap.toMatrix_one, hmat]
  -- The scalar `v ⬝ᵥ u` of the rank-one matrix is `f x`.
  have hdot : dotProduct (f ∘ b) (b.repr x) = f x := by
    rw [dotProduct]
    have h : (∑ i, (b.repr x) i * f (b i)) = f x := by
      conv_rhs => rw [← b.sum_repr x]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by simp [Function.comp_apply, mul_comm]
  rw [← LinearMap.det_toMatrix b (1 + f.smulRight x), hm, Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1), hdot, hf]
  rfl

end Work.Mostow
