import Mathlib
import Submission.Work.BMF.abel_ioc_step_bound
import Submission.Work.BMF.sum_Icc_sub_telescope

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Abel summation with the weight `1/n`

`Work.BMF.mr_direct.abel_inv_bound`: if the partial sums `∑_{j ∈ Ioc N k} a j` of a complex
sequence `a` are bounded by `B` for all `N < k ≤ M`, then the `1/n`-weighted sum satisfies

`‖∑_{n ∈ Ioc N M} (1/n) · a n‖ ≤ B · (1/M + 1/(N+1))`.

This is the discrete summation-by-parts (Abel) estimate with the weight `w n = 1/n`, whose total
variation over `{N+1, …, M}` is `1/(N+1) - 1/M ≤ 1/(N+1)`.  It is obtained by combining
* `Work.BMF.abel_ioc_step_bound` — the Abel step bound `‖∑ w n a n‖ ≤ B‖w M‖ + B ∑ ‖w n - w (n+1)‖`,
* the norm computation `‖(1/n : ℂ) - (1/(n+1) : ℂ)‖ = 1/n - 1/(n+1)`,
* and the telescoping `Work.BMF.sum_Icc_sub_telescope`
  `∑_{n ∈ Icc (N+1) (M-1)} (1/n - 1/(n+1)) = 1/(N+1) - 1/M`.
-/

namespace Work.BMF.mr_direct

theorem abel_inv_bound (a : ℕ → ℂ) (B : ℝ) (N M : ℕ) (hNM : N < M)
    (hpartial : ∀ k, N < k → k ≤ M → ‖∑ j ∈ Finset.Ioc N k, a j‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc N M, (((n : ℝ))⁻¹ : ℂ) * a n‖
      ≤ B * (1 / (M : ℝ) + 1 / ((N + 1 : ℕ) : ℝ)) := by
  classical
  set w : ℕ → ℝ := fun n => ((n : ℝ))⁻¹ with hw
  have hwn : ∀ n, w n = ((n : ℝ))⁻¹ := fun n => by rw [hw]
  -- `B` is nonnegative, since the hypothesis is instantiated at `k = N + 1 ≤ M`.
  have hB : 0 ≤ B := by
    have h1 := hpartial (N + 1) (Nat.lt_succ_self N) (by omega)
    exact le_trans (norm_nonneg _) h1
  -- Rewrite the target summand, a complex inverse of a natural, as a cast of a real.
  have hgoal_eq : (∑ n ∈ Finset.Ioc N M, (((n : ℝ))⁻¹ : ℂ) * a n)
      = ∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [hwn n, ← Complex.ofReal_inv]
  have hstep := Work.BMF.abel_ioc_step_bound a w B N M hNM hpartial
  rw [hgoal_eq]
  -- Norm of the top weight.
  have hwM : ‖(w M : ℂ)‖ = 1 / (M : ℝ) := by
    rw [hwn M, Complex.norm_of_nonneg (by positivity), one_div]
  -- Norm of the weight differences (positive real quantity, since `1 ≤ n`).
  have hdiff : ∀ n ∈ Finset.Icc (N + 1) (M - 1),
      ‖(w n : ℂ) - (w (n + 1) : ℂ)‖ = 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := by omega
    rw [hwn n, hwn (n + 1), ← Complex.ofReal_sub,
      Complex.norm_of_nonneg (by
        apply sub_nonneg.mpr
        exact inv_anti₀ (by positivity) (by push_cast; linarith)),
      one_div, one_div]
  -- Telescoping bound on the total variation of the weight.
  have hsum : ∑ n ∈ Finset.Icc (N + 1) (M - 1), (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))
      ≤ 1 / ((N + 1 : ℕ) : ℝ) := by
    have htel := Work.BMF.sum_Icc_sub_telescope (fun n : ℕ => 1 / (n : ℝ)) (N + 1) (M - 1)
      (by omega)
    rw [htel, show M - 1 + 1 = M from by omega]
    have hpos : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith
  calc ‖∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n‖
      ≤ B * ‖(w M : ℂ)‖
          + B * ∑ n ∈ Finset.Icc (N + 1) (M - 1), ‖(w n : ℂ) - (w (n + 1) : ℂ)‖ := hstep
    _ = B * (1 / (M : ℝ))
          + B * ∑ n ∈ Finset.Icc (N + 1) (M - 1), (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
          rw [hwM, Finset.sum_congr rfl hdiff]
    _ ≤ B * (1 / (M : ℝ)) + B * (1 / ((N + 1 : ℕ) : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hsum hB
          linarith
    _ = B * (1 / (M : ℝ) + 1 / ((N + 1 : ℕ) : ℝ)) := by ring

end Work.BMF.mr_direct
