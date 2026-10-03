import Mathlib

namespace Work.FIArea7

open Finset

/-- Reindexing a sum over `Icc 1 N` as a sum over `range N`:
`∑_{1 ≤ m ≤ N} f m = ∑_{i < N} f (i+1)`. -/
lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, f m = ∑ i ∈ Finset.range N, f (i + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) N, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- Discrete Abel (summation by parts) identity, in `range` form.  For `1 ≤ N`,
`∑_{i<N} w (i+1) * a (i+1)
   = w N * (∑_{i<N} a (i+1)) - ∑_{i<N-1} (w (i+2) - w (i+1)) * (∑_{j≤i} a (j+1))`.
This is `Finset.sum_range_by_parts` with the partial sums `∑_{j≤i} a (j+1)` of `a` appearing
against the forward differences of the weight `w`. -/
lemma abelRangeIdentity (a w : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ i ∈ Finset.range N, w (i + 1) * a (i + 1))
      = w N * (∑ i ∈ Finset.range N, a (i + 1))
        - ∑ i ∈ Finset.range (N - 1),
            (w (i + 2) - w (i + 1)) * (∑ j ∈ Finset.range (i + 1), a (j + 1)) := by
  have h := Finset.sum_range_by_parts (fun i => w (i + 1)) (fun i => a (i + 1)) N
  simp only [smul_eq_mul] at h
  rw [h, Nat.sub_add_cancel hN]

/-- The triangle-inequality estimate used in Abel summation: if the factors `S i` are all
bounded by `B ≥ 0` on `i ∈ range n`, then `‖∑_{i<n} u i * S i‖ ≤ B * ∑_{i<n} ‖u i‖`. -/
lemma norm_sum_mul_range_le (u S : ℕ → ℂ) (n : ℕ) (B : ℝ) (_hB : 0 ≤ B)
    (hS : ∀ i, i ∈ Finset.range n → ‖S i‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, u i * S i‖ ≤ B * ∑ i ∈ Finset.range n, ‖u i‖ := by
  calc ‖∑ i ∈ Finset.range n, u i * S i‖
      ≤ ∑ i ∈ Finset.range n, ‖u i * S i‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range n, ‖u i‖ * ‖S i‖ := by simp
    _ ≤ ∑ i ∈ Finset.range n, ‖u i‖ * B :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hS i hi) (norm_nonneg _))
    _ = (∑ i ∈ Finset.range n, ‖u i‖) * B := by rw [Finset.sum_mul]
    _ = B * ∑ i ∈ Finset.range n, ‖u i‖ := by ring

/-- Discrete summation by parts (Abel) for ℂ-valued sequences: if the partial sums
`A t = ∑_{m ∈ Icc 1 t} a m` are bounded by `B` for all `t ≤ N`, then
`‖∑_{m ≤ N} a m * w m‖ ≤ B * (‖w N‖ + ∑_{m ≤ N-1} ‖w (m+1) - w m‖)`.
Proof: `∑_{m ≤ N} (A m - A (m-1)) w m = A N w N + ∑_{m ≤ N-1} A m (w m - w (m+1))`
(e.g. via `Finset.sum_range_by_parts`). -/
theorem psiAbel (a w : ℕ → ℂ) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t : ℕ, t ≤ N → ‖∑ m ∈ Finset.Icc 1 t, a m‖ ≤ B) :
    ‖∑ m ∈ Finset.Icc 1 N, a m * w m‖
      ≤ B * (‖w N‖ + ∑ m ∈ Finset.Icc 1 (N - 1), ‖w (m + 1) - w m‖) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hz : (∑ m ∈ Finset.Icc 1 0, a m * w m) = 0 := by simp
    rw [hz, norm_zero]
    positivity
  · have hN1 : 1 ≤ N := hNpos
    rw [sum_Icc_one_eq_sum_range (fun m => a m * w m) N]
    have hcomm : (∑ i ∈ Finset.range N, a (i + 1) * w (i + 1))
        = ∑ i ∈ Finset.range N, w (i + 1) * a (i + 1) := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hcomm, abelRangeIdentity a w N hN1]
    have hSN : ‖∑ i ∈ Finset.range N, a (i + 1)‖ ≤ B := by
      rw [← sum_Icc_one_eq_sum_range a N]; exact h N le_rfl
    have hb1 : ‖w N * (∑ i ∈ Finset.range N, a (i + 1))‖ ≤ ‖w N‖ * B := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hSN (norm_nonneg _)
    have hb2 : ‖∑ i ∈ Finset.range (N - 1),
          (w (i + 2) - w (i + 1)) * (∑ j ∈ Finset.range (i + 1), a (j + 1))‖
        ≤ B * ∑ i ∈ Finset.range (N - 1), ‖w (i + 2) - w (i + 1)‖ := by
      refine norm_sum_mul_range_le _ _ (N - 1) B hB ?_
      intro i hi
      simp only [Finset.mem_range] at hi
      have hi1 : i + 1 ≤ N := by omega
      rw [← sum_Icc_one_eq_sum_range a (i + 1)]
      exact h (i + 1) hi1
    have hlast : (∑ m ∈ Finset.Icc 1 (N - 1), ‖w (m + 1) - w m‖)
        = ∑ i ∈ Finset.range (N - 1), ‖w (i + 2) - w (i + 1)‖ := by
      rw [sum_Icc_one_eq_sum_range (fun m => ‖w (m + 1) - w m‖) (N - 1)]
    rw [hlast]
    refine le_trans (norm_sub_le _ _) ?_
    refine le_trans (add_le_add hb1 hb2) ?_
    exact le_of_eq (by ring)

end Work.FIArea7
