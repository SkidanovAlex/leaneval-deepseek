import Mathlib
import Submission.Work.BMF.ioc_abel_identity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Abel summation step bound on `Ioc N M`

If the partial sums `∑_{j ∈ Ioc N k} a j` of a sequence `a : ℕ → ℂ` are bounded by `B` for every
`N < k ≤ M`, then for real weights `w`

`‖∑_{n ∈ Ioc N M} w n * a n‖ ≤ B * ‖w M‖ + B * ∑_{n ∈ Icc (N+1) (M-1)} ‖w n - w (n+1)‖`.

This is the discrete summation-by-parts (Abel) estimate: writing `A k = ∑_{j ∈ Ioc N k} a j`, the
`ioc_abel_identity` gives `∑_{n ∈ Ioc N M} w n a n = w M A M + ∑_{n ∈ Ioc N (M-1)} (w n - w (n+1)) A n`,
and both `‖A M‖ ≤ B` and `‖A n‖ ≤ B` for `n ∈ Ioc N (M-1)` close the bound.
-/

namespace Work.BMF

theorem abel_ioc_step_bound (a : ℕ → ℂ) (w : ℕ → ℝ) (B : ℝ) (N M : ℕ)
    (hNM : N < M)
    (hpartial : ∀ k, N < k → k ≤ M → ‖∑ j ∈ Finset.Ioc N k, a j‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n‖
      ≤ B * ‖(w M : ℂ)‖
        + B * ∑ n ∈ Finset.Icc (N + 1) (M - 1), ‖(w n : ℂ) - (w (n + 1) : ℂ)‖ := by
  classical
  -- `v` is the complexification of the real weight `w`; `A` the partial sums of `a`.
  set v : ℕ → ℂ := fun n => (w n : ℂ) with hv
  set A : ℕ → ℂ := fun k => ∑ j ∈ Finset.Ioc N k, a j with hA
  change ‖∑ n ∈ Finset.Ioc N M, v n * a n‖
      ≤ B * ‖v M‖ + B * ∑ n ∈ Finset.Icc (N + 1) (M - 1), ‖v n - v (n + 1)‖
  have hA0 : A N = 0 := by simp [hA]
  have hstep : ∀ k, N ≤ k → A (k + 1) = A k + a (k + 1) := by
    intro k hk
    simp only [hA]
    exact Finset.sum_Ioc_succ_top hk (fun j => a j)
  have hid := ioc_abel_identity a v A N M hA0 hstep hNM
  have hIocIcc : Finset.Ioc N (M - 1) = Finset.Icc (N + 1) (M - 1) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hAM : ‖A M‖ ≤ B := by simpa only [hA] using hpartial M hNM le_rfl
  have hD : ∀ n ∈ Finset.Ioc N (M - 1), ‖(v n - v (n + 1)) * A n‖ ≤ B * ‖v n - v (n + 1)‖ := by
    intro n hn
    have hnn : N < n := (Finset.mem_Ioc.mp hn).1
    have hnM : n ≤ M := le_trans (Finset.mem_Ioc.mp hn).2 (Nat.sub_le M 1)
    have hAn : ‖A n‖ ≤ B := by simpa only [hA] using hpartial n hnn hnM
    rw [norm_mul]
    calc ‖v n - v (n + 1)‖ * ‖A n‖ ≤ ‖v n - v (n + 1)‖ * B :=
          mul_le_mul_of_nonneg_left hAn (norm_nonneg _)
      _ = B * ‖v n - v (n + 1)‖ := mul_comm _ _
  rw [hid]
  calc ‖v M * A M + ∑ n ∈ Finset.Ioc N (M - 1), (v n - v (n + 1)) * A n‖
      ≤ ‖v M * A M‖ + ‖∑ n ∈ Finset.Ioc N (M - 1), (v n - v (n + 1)) * A n‖ :=
        norm_add_le _ _
    _ ≤ B * ‖v M‖ + B * ∑ n ∈ Finset.Ioc N (M - 1), ‖v n - v (n + 1)‖ := by
        apply add_le_add
        · rw [norm_mul]
          calc ‖v M‖ * ‖A M‖ ≤ ‖v M‖ * B := mul_le_mul_of_nonneg_left hAM (norm_nonneg _)
            _ = B * ‖v M‖ := mul_comm _ _
        · calc ‖∑ n ∈ Finset.Ioc N (M - 1), (v n - v (n + 1)) * A n‖
              ≤ ∑ n ∈ Finset.Ioc N (M - 1), ‖(v n - v (n + 1)) * A n‖ := norm_sum_le _ _
            _ ≤ ∑ n ∈ Finset.Ioc N (M - 1), B * ‖v n - v (n + 1)‖ := Finset.sum_le_sum hD
            _ = B * ∑ n ∈ Finset.Ioc N (M - 1), ‖v n - v (n + 1)‖ := by rw [Finset.mul_sum]
    _ = B * ‖v M‖ + B * ∑ n ∈ Finset.Icc (N + 1) (M - 1), ‖v n - v (n + 1)‖ := by rw [hIocIcc]

end Work.BMF
