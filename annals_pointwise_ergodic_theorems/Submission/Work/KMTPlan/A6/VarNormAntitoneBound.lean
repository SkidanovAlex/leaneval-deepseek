/-
# The variational norm of a sequence with an antitone controlling scale

If the successive differences of a sequence `x : ℕ → ℂ` are dominated by the decrements of a
nonnegative, antitone, bounded sequence `u : ℕ → ℝ`,

  `‖x (n+1) - x n‖ ≤ K * (u n - u (n+1))`,

then the whole `r`-variational norm (`r ≥ 1`) of `x` is bounded by `B + K ρ`, where `B` bounds
`‖x n‖` and `ρ` bounds `u`.  This is the elementary "telescoping along a monotone subsequence"
estimate used by the A6 area to control the clamped averages whose scale parameter is frozen.
-/
import Mathlib
import Submission.VarPrep

namespace Work.KMTPlan.A6

open scoped ENNReal NNReal

theorem VarNormAntitoneBound
    {r : NNReal} (hr : 1 ≤ r) {u : ℕ → ℝ} {x : ℕ → ℂ} {B K ρ : ℝ}
    (hρ : 0 ≤ ρ) (hu0 : ∀ n, 0 ≤ u n) (huρ : ∀ n, u n ≤ ρ) (hmono : Antitone u)
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hsup : ∀ n, ‖x n‖ ≤ B)
    (hstep : ∀ n, ‖x (n + 1) - x n‖ ≤ K * (u n - u (n + 1))) :
    PointwiseErgodicTheorems.variationalNorm r x ≤ ENNReal.ofReal (B + K * ρ) := by
  -- The supremum of the norms of the entries is at most `B`.
  have hsupB : (⨆ n, ‖x n‖ₑ) ≤ ENNReal.ofReal B := by
    refine iSup_le (fun n => ?_)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hsup n)
  -- Telescoping along a monotone subsequence: the `ℓ¹` norm of the increments is at most `K ρ`.
  have key : ∀ (J : ℕ) (N : ℕ → ℕ), Monotone N →
      ∑ i : Fin J, ‖x (N (i + 1)) - x (N i)‖ ≤ K * ρ := by
    intro J N hN
    have hterm : ∀ i : Fin J,
        ‖x (N (i + 1)) - x (N i)‖ ≤ K * (u (N i) - u (N (i + 1))) := by
      intro i
      have hle : N i ≤ N (i + 1) := hN (Nat.le_succ _)
      have htel : x (N (i + 1)) - x (N i)
          = ∑ k ∈ Finset.Ico (N i) (N (i + 1)), (x (k + 1) - x k) :=
        (Finset.sum_Ico_sub x hle).symm
      rw [htel]
      calc ‖∑ k ∈ Finset.Ico (N i) (N (i + 1)), (x (k + 1) - x k)‖
          ≤ ∑ k ∈ Finset.Ico (N i) (N (i + 1)), ‖x (k + 1) - x k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.Ico (N i) (N (i + 1)), K * (u k - u (k + 1)) :=
            Finset.sum_le_sum (fun k _ => hstep k)
        _ = K * ∑ k ∈ Finset.Ico (N i) (N (i + 1)), (u k - u (k + 1)) := by
            rw [Finset.mul_sum]
        _ = K * (u (N i) - u (N (i + 1))) := by
            congr 1
            have hneg : ∑ k ∈ Finset.Ico (N i) (N (i + 1)), (u k - u (k + 1))
                = - ∑ k ∈ Finset.Ico (N i) (N (i + 1)), (u (k + 1) - u k) := by
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl (fun k _ => by ring)
            rw [hneg, Finset.sum_Ico_sub u hle]
            ring
    calc ∑ i : Fin J, ‖x (N (i + 1)) - x (N i)‖
        ≤ ∑ i : Fin J, K * (u (N i) - u (N (i + 1))) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = K * ∑ i : Fin J, (u (N i) - u (N (i + 1))) := by rw [Finset.mul_sum]
      _ = K * (u (N 0) - u (N J)) := by
          congr 1
          rw [Fin.sum_univ_eq_sum_range (fun i => u (N i) - u (N (i + 1))) J,
              Finset.sum_range_sub' (fun i => u (N i)) J]
      _ ≤ K * ρ := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact (sub_le_self _ (hu0 (N J))).trans (huρ (N 0))
  -- The variation part is at most `K ρ`.
  have hvar : (⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
      ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => x (N (i + 1)) - x (N i))‖)
      ≤ ENNReal.ofReal (K * ρ) := by
    refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
    exact ENNReal.ofReal_le_ofReal
      ((Submission.PointwiseErgodicTheorems.norm_toLp_le_sum_norm hr _).trans (key J N hN))
  have hmain : PointwiseErgodicTheorems.variationalNorm r x
      ≤ ENNReal.ofReal B + ENNReal.ofReal (K * ρ) := by
    show (⨆ n, ‖x n‖ₑ) + (⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
      ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => x (N (i + 1)) - x (N i))‖) ≤ _
    exact add_le_add hsupB hvar
  calc PointwiseErgodicTheorems.variationalNorm r x
      ≤ ENNReal.ofReal B + ENNReal.ofReal (K * ρ) := hmain
    _ = ENNReal.ofReal (B + K * ρ) :=
        (ENNReal.ofReal_add hB (mul_nonneg hK hρ)).symm

end Work.KMTPlan.A6
