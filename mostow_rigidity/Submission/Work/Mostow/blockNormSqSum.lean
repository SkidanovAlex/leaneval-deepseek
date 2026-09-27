import Mathlib
import Submission.Work.Mostow.rescaledPoint
import Submission.Work.Mostow.dominationTransfer

namespace Work.Mostow

/-- If `u` and `v` are orthonormal vectors of a real inner product space, then
`‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2`. -/
lemma norm_sq_smul_add_smul_of_orthonormal {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {u v : F} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (a b : ℝ) :
    ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  have horth : inner ℝ (a • u) (b • v) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, huv, mul_zero, mul_zero]
  have hn1 : ‖a • u‖ ^ 2 = a ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu]; ring
  have hn2 : ‖b • v‖ ^ 2 = b ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hv]; ring
  rw [horth, hn1, hn2]; ring

theorem blockNormSqSum (m : ℕ)
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (W : Submission.Mostow.E m) :
    ‖W‖ ^ 2 = ∑ i : Fin (m / 2),
      ‖(inner ℝ (e (i, Fin.castSucc 0)) W) • e (i, Fin.castSucc 0) +
        (inner ℝ (e (i, 1)) W) • e (i, 1)‖ ^ 2 := by
  rw [← OrthonormalBasis.sum_sq_inner_right e W, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.castSucc_zero]
  rw [Fin.sum_univ_two]
  exact (norm_sq_smul_add_smul_of_orthonormal
    (e.orthonormal.1 (i, 0)) (e.orthonormal.1 (i, 1))
    (e.orthonormal.2 (by simp)) _ _).symm

end Work.Mostow
