import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSExp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000



/-- **The pointwise bound** `(D_z^j (radS α f)(z))² w(z)² ≤ SmajA α f j K z` on `(0,∞)`. -/
theorem radS_sq_le_SmajA_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f)
    (hl12 : Work.Construction.L12 f 0 = 0) {j : ℕ} (hj : j ≤ 3) {K : ℝ} (hKnn : 0 ≤ K)
    (hKbd : ∀ b ≤ 4, ∀ z ∈ IoiA,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K) :
    ∀ z ∈ IoiA, (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
      * (Work.Spaces.w z) ^ 2 ≤ Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j K z := by
  have hC0 : ∀ b, ((j.choose b : ℕ) : ℝ) ^ 2 = ((j.choose b : ℝ)) ^ 2 := by
    intro b; push_cast; ring
  intro z hz
  rw [radS_DzdIter_eq_O α hα hα1 hO hmem5 hl12 hj z hz,
    Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA]
  set S1 : ℝ := Work.FTS.CoercivityFix.Transfer.E2pkg.W1 α f j z with hS1
  set S2 : ℝ := Work.FTS.CoercivityFix.Transfer.E2pkg.W2 α f j z with hS2
  set S3 : ℝ := Work.FTS.CoercivityFix.Transfer.E2pkg.W3 α f j z with hS3
  have hsq : (-S1 + S2 + S3) ^ 2 ≤ 3 * (S1 ^ 2 + S2 ^ 2 + S3 ^ 2) := by
    nlinarith [sq_nonneg (S1 - S2), sq_nonneg (S2 - S3), sq_nonneg (S3 + S1)]
  have hw_nn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hS1b : S1 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
      * (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) := by
    have hcs : S1 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter (b + 1)
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) := by
      rw [hS1, Work.FTS.CoercivityFix.Transfer.E2pkg.W1]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hK1 : (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter (b + 1)
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun b hb => ?_
      have hbj : b + 1 ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      have hb1 : |Work.Elliptic.DzdIter (b + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
        hKbd (b + 1) hbj z hz
      rw [mul_pow, hC0 b]
      exact mul_le_mul_of_nonneg_left
        (sq_le_sq' (abs_le.mp hb1).1 (abs_le.mp hb1).2) (sq_nonneg _)
    have hSnn : 0 ≤ (∑ b ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    calc S1 ^ 2 ≤ _ * (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) := hcs
      _ ≤ ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) :=
          mul_le_mul_of_nonneg_right hK1 hSnn
  have hS2b : S2 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
      * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) := by
    have hcs : S2 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter b
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) := by
      rw [hS2, Work.FTS.CoercivityFix.Transfer.E2pkg.W2]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hK2 : (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter b
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun b hb => ?_
      have hbj : b ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      have hb1 : |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
        hKbd b hbj z hz
      rw [mul_pow, hC0 b]
      exact mul_le_mul_of_nonneg_left
        (sq_le_sq' (abs_le.mp hb1).1 (abs_le.mp hb1).2) (sq_nonneg _)
    have hSnn : 0 ≤ (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    calc S2 ^ 2 ≤ _ * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) := hcs
      _ ≤ ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
          * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) :=
          mul_le_mul_of_nonneg_right hK2 hSnn
  have hS3b : S3 ^ 2 = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
      * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2) := by
    rw [hS3, Work.FTS.CoercivityFix.Transfer.E2pkg.W3]; ring
  have h1 : (S1 ^ 2 + S2 ^ 2 + S3 ^ 2) * (Work.Spaces.w z) ^ 2
      ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
        + (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
          * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := by
    have e1 : (S1 ^ 2) * (Work.Spaces.w z) ^ 2
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2) := by
      calc S1 ^ 2 * (Work.Spaces.w z) ^ 2
          ≤ (((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2))
              * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hS1b hw_nn
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * ((∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2) := by rw [← Finset.sum_mul]
    have e2 : (S2 ^ 2) * (Work.Spaces.w z) ^ 2
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      calc S2 ^ 2 * (Work.Spaces.w z) ^ 2
          ≤ (((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2))
              * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hS2b hw_nn
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * ((∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
            rw [← Finset.sum_mul]
    have e3 : (S3 ^ 2) * (Work.Spaces.w z) ^ 2
        = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
          * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := by
      rw [hS3b]; ring
    linarith [e1, e2, e3.le]
  have h2 := mul_le_mul_of_nonneg_right hsq hw_nn
  linarith [h1, h2]

end Work.FTS.StrongEps.EpsE4Thr.E2O
