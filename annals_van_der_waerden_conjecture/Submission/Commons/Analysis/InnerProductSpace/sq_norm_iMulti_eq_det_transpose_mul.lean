import Mathlib.Analysis.InnerProductSpace.ExteriorPower

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

/-- The Gram matrix of the real column vectors of an integer matrix `C` (viewed in
`EuclideanSpace ℝ (Fin N)`) is the real cast of `Matrix.transpose C * C`. -/
lemma gram_cast_eq_map_transpose_mul {N k : ℕ} (C : Matrix (Fin N) (Fin k) ℤ) :
    Matrix.gram ℝ
        (fun j : Fin k => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i : Fin N => (C i j : ℝ)))
      = (Matrix.transpose C * C).map (fun z : ℤ => (z : ℝ)) := by
  classical
  let v : Fin k → EuclideanSpace ℝ (Fin N) :=
    fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i : Fin N => (C i j : ℝ))
  have hv : ∀ (j : Fin k) (x : Fin N), (v j).ofLp x = (C x j : ℝ) := by
    intro j x
    simp [v, WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
  change Matrix.gram ℝ v = (Matrix.transpose C * C).map (fun z : ℤ => (z : ℝ))
  ext i j
  rw [Matrix.gram_apply, Matrix.map_apply, Matrix.mul_apply]
  rw [PiLp.inner_apply]
  simp only [hv]
  rw [show ((↑(∑ x : Fin N, C.transpose i x * C x j) : ℝ))
        = ∑ x : Fin N, (C x i : ℝ) * (C x j : ℝ) from by
      push_cast
      apply Finset.sum_congr rfl
      intro x _
      rw [Matrix.transpose_apply]]
  apply Finset.sum_congr rfl
  intro x _
  rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- The squared norm of the exterior product (wedge) of the columns of an integer matrix `C` (viewed as vectors of `EuclideanSpace ℝ (Fin N)`) equals the determinant of the Gram matrix `Matrix.transpose C * C`, cast to `ℝ`. Proof: `‖ιMulti ℝ k v‖ ^ 2 = (Matrix.gram ℝ v).det` (Mathlib `exteriorPower.inner_ιMulti_self` together with `inner_self_eq_norm_sq_to_K`), and the Gram matrix of the columns of `C` is the cast of `Matrix.transpose C * C`. -/
theorem sq_norm_iMulti_eq_det_transpose_mul {N k : ℕ} (C : Matrix (Fin N) (Fin k) ℤ) :
    ‖exteriorPower.ιMulti ℝ k
        (fun j : Fin k => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i : Fin N => (C i j : ℝ)))‖ ^ 2
      = ((Matrix.transpose C * C).map (fun z : ℤ => (z : ℝ))).det := by
  classical
  let v : Fin k → EuclideanSpace ℝ (Fin N) :=
    fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i : Fin N => (C i j : ℝ))
  have hgram : Matrix.gram ℝ v = (Matrix.transpose C * C).map (fun z : ℤ => (z : ℝ)) :=
    gram_cast_eq_map_transpose_mul C
  change ‖exteriorPower.ιMulti ℝ k v‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq (exteriorPower.ιMulti ℝ k v),
    exteriorPower.inner_ιMulti_self v, hgram]

end Commons.Analysis.InnerProductSpace