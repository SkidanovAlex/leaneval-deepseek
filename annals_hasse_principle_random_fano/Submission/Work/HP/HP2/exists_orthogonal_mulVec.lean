import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.HP2

open MeasureTheory

/-- `rNorm` is the square root of the Euclidean dot product of a vector with itself. -/
private lemma rNorm_eq_sqrt_dotProduct {n : ℕ} (v : Fin n → ℝ) :
    rNorm v = Real.sqrt (dotProduct v v) := by
  simp only [rNorm, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun i _ => sq (v i)

/-- The real inner product on `EuclideanSpace ℝ (Fin n)` is the sum of the products of
the coordinates. -/
private lemma inner_euclidean_eq_sum {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u v = ∑ i, u.ofLp i * v.ofLp i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_orthogonal_mulVec (m : ℕ) (e : Fin (m + 1) → ℝ) (he : Work.HP.rNorm e = 1) :
    ∃ M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
      M.transpose * M = 1 ∧
      (∀ x : Fin (m + 1) → ℝ, Work.HP.rNorm (M.mulVec x) = Work.HP.rNorm x) ∧
      M.mulVec (Pi.single 0 (1 : ℝ)) = e ∧
      MeasureTheory.Measure.map (fun x : Fin (m + 1) → ℝ => M.mulVec x) MeasureTheory.volume
        = MeasureTheory.volume := by
  classical
  -- The unit vector `e` viewed as an element of `EuclideanSpace ℝ (Fin (m+1))`.
  set x : EuclideanSpace ℝ (Fin (m + 1)) := WithLp.toLp 2 e with hxdef
  have hx : ‖x‖ = 1 := by
    rw [hxdef, EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    simpa [rNorm] using he
  -- Extend `x` to an orthonormal basis `b` with `b 0 = x`.
  let v : Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1)) := fun _ => x
  have hvorth : Orthonormal ℝ (({0} : Set (Fin (m + 1))).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i.1 = 0 := Set.mem_singleton_iff.mp i.2
    have hj : j.1 = 0 := Set.mem_singleton_iff.mp j.2
    have hij : i = j := Subtype.ext (by rw [hi, hj])
    subst hij
    rw [ite_eq_left rfl]
    have hval : (({0} : Set (Fin (m + 1))).domRestrict v) i = x := rfl
    rw [hval, inner_self_eq_norm_sq_to_K, hx]
    norm_num
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (E := EuclideanSpace ℝ (Fin (m + 1))) (ι := Fin (m + 1)) (v := v) (s := {0})
      (by rw [finrank_euclideanSpace]) hvorth
  have hb0 : b 0 = x := by
    simpa using hb 0 (by simp)
  -- The matrix whose `j`-th column is `b j`.
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun i j => (b j).ofLp i with hMdef
  have hM_apply : ∀ i j, M i j = (b j).ofLp i := by
    intro i j
    rw [hMdef]
  -- `M` is orthogonal: its columns are orthonormal.
  have hMM : M.transpose * M = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    simp only [hM_apply]
    rw [← orthonormal_iff_ite.mp b.orthonormal i j, inner_euclidean_eq_sum]
  refine ⟨M, hMM, ?_, ?_, ?_⟩
  · -- `M` preserves the Euclidean norm.
    intro y
    rw [rNorm_eq_sqrt_dotProduct, rNorm_eq_sqrt_dotProduct]
    congr 1
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose M (M.mulVec y),
      Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
  · -- The first column of `M` is `e`.
    rw [Matrix.mulVec_single_one]
    ext i
    rw [Matrix.col_apply]
    simp only [hM_apply]
    rw [hb0, hxdef, WithLp.ofLp_toLp]
  · -- `M.mulVec` preserves Lebesgue measure, since `|det M| = 1`.
    have hdet1 : M.det * M.det = 1 := by
      have h := congrArg Matrix.det hMM
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      exact h
    have hdet : M.det ≠ 0 := by
      intro h; rw [h, zero_mul] at hdet1; exact zero_ne_one hdet1
    have habs : |M.det| = 1 := by
      have h2 : M.det ^ 2 = 1 := by rw [sq]; exact hdet1
      rcases sq_eq_one_iff.mp h2 with h | h
      · rw [h, abs_one]
      · rw [h, abs_neg, abs_one]
    have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) hdet
    rw [show (fun y : Fin (m + 1) → ℝ => M.mulVec y) = ⇑(Matrix.toLin' M) from
      funext fun y => (Matrix.toLin'_apply M y).symm]
    rw [hmap, abs_inv, habs, inv_one, ENNReal.ofReal_one, one_smul]

end Work.HP.HP2
