import Mathlib
import Submission.Work.BMF.abel_ioc_step_bound
import Submission.Work.BMF.sum_Icc_sub_telescope

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Abel summation bound on `Ioc N M`

For `a : ℕ → ℂ`, a real weight `w` that is nonnegative and nonincreasing on `{N+1, …, M}`,
and `B` bounding the partial sums `∑_{j ∈ Ioc N k} a j` for all `N < k ≤ M`, the weighted sum
`∑_{n ∈ Ioc N M} w n · a n` is bounded by `B · w (N+1)`.

This is the classical summation-by-parts (Abel) estimate: the discrete Abel identity rewrites the
weighted sum using the partial sums of `a`, and since the weight is nonincreasing at least as fast
as its own total variation, the bound telescopes to `B · w (N+1)`.

The two ingredients are proved separately:
* `Work.BMF.abel_ioc_step_bound` — the Abel step bound
  `‖∑_{n ∈ Ioc N M} w n a n‖ ≤ B ‖w M‖ + B ∑_{n ∈ Icc (N+1) (M-1)} ‖w n - w (n+1)‖`;
* `Work.BMF.sum_Icc_sub_telescope` — the telescoping
  `∑_{n ∈ Icc a b} (w n - w (n+1)) = w a - w (b+1)` for `a ≤ b + 1`.
-/

namespace Work.BMF

open Finset

/-- **Abel summation bound.** If the partial sums `∑_{j ∈ Ioc N k} a j` (`N < k ≤ M`) are bounded
by `B` and `w` is nonnegative and nonincreasing on `Ioc N M`, then
`‖∑_{n ∈ Ioc N M} w n · a n‖ ≤ B · w (N + 1)`. -/
theorem abel_ioc_bound (a : ℕ → ℂ) (w : ℕ → ℝ) (N M : ℕ) (B : ℝ)
    (hNM : N < M) (hB : 0 ≤ B)
    (hw0 : ∀ n ∈ Finset.Ioc N M, 0 ≤ w n)
    (hwmono : ∀ n, N ≤ n → n < M → w (n + 1) ≤ w n)
    (hpartial : ∀ k, N < k → k ≤ M → ‖∑ j ∈ Finset.Ioc N k, a j‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n‖ ≤ B * w (N + 1) := by
  have hstep := abel_ioc_step_bound a w B N M hNM hpartial
  have hwM : 0 ≤ w M := hw0 M (by rw [Finset.mem_Ioc]; exact ⟨hNM, le_rfl⟩)
  have h1 : ‖(w M : ℂ)‖ = w M := Complex.norm_of_nonneg hwM
  have h2 : ∀ n ∈ Finset.Icc (N + 1) (M - 1),
      ‖(w n : ℂ) - (w (n + 1) : ℂ)‖ = w n - w (n + 1) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hle : w (n + 1) ≤ w n := hwmono n (by omega) (by omega)
    rw [← Complex.ofReal_sub]
    exact Complex.norm_of_nonneg (sub_nonneg.mpr hle)
  have h3 : ∑ n ∈ Finset.Icc (N + 1) (M - 1), (w n - w (n + 1)) = w (N + 1) - w M := by
    have hh := sum_Icc_sub_telescope w (N + 1) (M - 1) (by omega)
    rwa [show M - 1 + 1 = M by omega] at hh
  calc ‖∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n‖
      ≤ B * ‖(w M : ℂ)‖
          + B * ∑ n ∈ Finset.Icc (N + 1) (M - 1), ‖(w n : ℂ) - (w (n + 1) : ℂ)‖ := hstep
    _ = B * w M + B * ∑ n ∈ Finset.Icc (N + 1) (M - 1), (w n - w (n + 1)) := by
        rw [h1, Finset.sum_congr rfl h2]
    _ = B * w M + B * (w (N + 1) - w M) := by rw [h3]
    _ = B * w (N + 1) := by ring

end Work.BMF
