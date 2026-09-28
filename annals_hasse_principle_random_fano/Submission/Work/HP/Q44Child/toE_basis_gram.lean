import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs

namespace Work.HP.Q44Child

open scoped RealInnerProductSpace Matrix

/-- For any `ℤ`-basis `b` of `ℤ^5`, the images `toE (b i)` form an `ℝ`-linearly independent
family in `EuclideanSpace ℝ (Fin 5)`, and their Gram matrix has determinant `1`.

Both facts follow from the computation
`gram ℝ (toE ∘ b) = mᴴ * m` with `m i j = ((b j) i : ℝ)`, whose determinant is `(det m) ^ 2`;
since `m` is the reduction mod `ℝ` of the unimodular change–of–basis matrix of `b`,
`det m = ±1`. -/
theorem toE_basis_gram (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) :
    LinearIndependent ℝ (fun i : Fin 5 => Work.HP.Q44Child.toE (b i)) ∧
    (Matrix.gram ℝ (fun i : Fin 5 => Work.HP.Q44Child.toE (b i))).det = 1 := by
  set m : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of (fun i j : Fin 5 => ((b j) i : ℝ)) with hm_def
  have hgram : Matrix.gram ℝ (fun i : Fin 5 => Work.HP.Q44Child.toE (b i)) = mᴴ * m := by
    have h := Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin 5) ℝ)
      (fun i : Fin 5 => Work.HP.Q44Child.toE (b i))
    rw [hm_def]
    simpa only [EuclideanSpace.basisFun_repr, toE_ofLp] using h
  have hunit : IsUnit ((Pi.basisFun ℤ (Fin 5)).toMatrix b).det :=
    Matrix.isUnit_det_of_left_inverse
      (Module.Basis.toMatrix_mul_toMatrix_flip b (Pi.basisFun ℤ (Fin 5)))
  have hMdet : ((Pi.basisFun ℤ (Fin 5)).toMatrix b).det = 1
      ∨ ((Pi.basisFun ℤ (Fin 5)).toMatrix b).det = -1 := Int.isUnit_iff.mp hunit
  have hm : m = ((Pi.basisFun ℤ (Fin 5)).toMatrix b).map (Int.castRingHom ℝ) := by
    rw [hm_def]
    ext i j
    simp [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hsq : m.det * m.det = 1 := by
    have h2 : m.det = (((Pi.basisFun ℤ (Fin 5)).toMatrix b).det : ℝ) := by
      rw [hm]
      exact (RingHom.map_det (Int.castRingHom ℝ)
        ((Pi.basisFun ℤ (Fin 5)).toMatrix b)).symm
    rw [h2]
    rcases hMdet with h | h <;> rw [h] <;> norm_num
  have hdet : (mᴴ * m).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial]
    exact hsq
  constructor
  · exact Matrix.linearIndependent_of_det_gram_ne_zero (by rw [hgram, hdet]; norm_num)
  · rw [hgram, hdet]

end Work.HP.Q44Child
