import Mathlib.RingTheory.PicardGroup
import Submission.Commons.LinearAlgebra.InnerProductSpace.singularValues_zero_mul_norm_le

open Module InnerProductSpace

namespace Commons.LinearAlgebra.Matrix

/-- **Large values bound (general finite index types).** Let `M` be a complex matrix with
rows indexed by `ι` and columns by `κ`, and let `b` be a vector with `‖b j‖ ≤ 1` for all `j`.
If every one of the `ι`-coordinates of `M b` has modulus at least `V > 0`, then
`card ι * V ^ 2` is at most the square of the largest singular value of `M` times `card κ`. -/
theorem spectral_large_values_bound_fintype {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ ℂ) (b : EuclideanSpace ℂ κ) (V : ℝ) (hV : 0 < V)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hval : ∀ t : ι, V ≤ ‖∑ j, M t j * b j‖) :
    (Fintype.card ι : ℝ) * V ^ 2
      ≤ ((Matrix.toEuclideanLin M).singularValues 0) ^ 2 * (Fintype.card κ : ℝ) := by
  set σ := (Matrix.toEuclideanLin M).singularValues 0 with hσdef
  have hσ0 : 0 ≤ σ := (Matrix.toEuclideanLin M).singularValues_nonneg 0
  have hcoord : ∀ t : ι, (Matrix.toEuclideanLin M b) t = ∑ j, M t j * b j := by
    intro t
    rw [← WithLp.toLp_ofLp (p := 2) (x := Matrix.toEuclideanLin M b)]
    rw [Matrix.ofLp_toLpLin]
    rfl
  have hnorm : ‖Matrix.toEuclideanLin M b‖ ^ 2 = ∑ t, ‖∑ j, M t j * b j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro t _
    rw [hcoord t]
  have hV2 : (Fintype.card ι : ℝ) * V ^ 2 ≤ ‖Matrix.toEuclideanLin M b‖ ^ 2 := by
    rw [hnorm]
    have hc : (Fintype.card ι : ℝ) * V ^ 2 = ∑ _t : ι, V ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hc]
    apply Finset.sum_le_sum
    intro t _
    nlinarith [hval t, hV, norm_nonneg (∑ j, M t j * b j)]
  have hb_norm : ‖b‖ ^ 2 ≤ (Fintype.card κ : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ j, ‖b j‖ ^ 2 ≤ ∑ _j : κ, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => by nlinarith [hb j, norm_nonneg (b j)])
      _ = (Fintype.card κ : ℝ) := by simp
  have hkey := Commons.LinearAlgebra.InnerProductSpace.singularValues_zero_mul_norm_le
    (Matrix.toEuclideanLin M) b
  have hupper : ‖Matrix.toEuclideanLin M b‖ ^ 2 ≤ σ ^ 2 * (Fintype.card κ : ℝ) := by
    have h2 : ‖Matrix.toEuclideanLin M b‖ ^ 2 ≤ (σ * ‖b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by simpa [hσdef] using hkey) 2
    rw [mul_pow] at h2
    nlinarith [h2, hb_norm, hσ0, sq_nonneg σ]
  linarith [hV2, hupper]

end Commons.LinearAlgebra.Matrix