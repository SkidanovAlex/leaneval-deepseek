import Mathlib
import Submission.Work.OddBound.indexTransfer.Infra
import Submission.Work.OddBound.polygon.polygon_energy_aux

namespace Work.OddBound.indexTransfer

/-- **Splitting an interval integral over the uniform partition.**

For a partition of the interval with endpoints `i * T / N` (`i = 0, …, N`), which runs
from `0` to `T`, the sum of the oriented interval integrals over the successive pieces
telescopes to the integral over the whole interval. The sign of `T` is irrelevant: the
oriented interval integral adds up along any chain of points.

This is the `Fin N`-indexed form of Mathlib's `intervalIntegral.sum_integral_adjacent_intervals`. -/
theorem sum_fin_integral_chain_partition (f : ℝ → ℝ) {T : ℝ} {N : ℕ} (hN : 0 < N)
    (h : ∀ i : Fin N, IntervalIntegrable f MeasureTheory.volume ((i : ℝ) * T / N)
        (((i : ℝ) + 1) * T / N)) :
    ∑ i : Fin N, ∫ t in ((i : ℝ) * T / N)..(((i : ℝ) + 1) * T / N), f t
      = ∫ t in (0 : ℝ)..T, f t := by
  -- Index the chain of partition points by `ℕ` rather than by `Fin N`; this also exposes
  -- the upper endpoint of the `k`-th piece as `(k + 1) * T / N` (with `k + 1` in `ℕ`),
  -- which is the form required by the chaining lemma.
  have key : ∀ k < N, IntervalIntegrable f MeasureTheory.volume ((k : ℝ) * T / N)
      (((k + 1 : ℕ) : ℝ) * T / N) := by
    intro k hk
    rw [Nat.cast_succ]
    exact h ⟨k, hk⟩
  have hN' : ((N : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  calc ∑ i : Fin N, ∫ t in ((i : ℝ) * T / N)..(((i : ℝ) + 1) * T / N), f t
      = ∑ k ∈ Finset.range N, ∫ t in ((k : ℝ) * T / N)..(((k : ℝ) + 1) * T / N), f t :=
        Fin.sum_univ_eq_sum_range
          (fun k : ℕ => ∫ t in ((k : ℝ) * T / N)..(((k : ℝ) + 1) * T / N), f t) N
    _ = ∑ k ∈ Finset.range N, ∫ t in ((k : ℝ) * T / N)..(((k + 1 : ℕ) : ℝ) * T / N), f t := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Nat.cast_succ]
    _ = ∫ t in ((0 : ℕ) : ℝ) * T / N..(((N : ℕ) : ℝ) * T / N), f t :=
        intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) * T / N) key
    _ = ∫ t in (0 : ℝ)..T, f t := by
        rw [Nat.cast_zero, zero_mul, zero_div, mul_div_cancel_left₀ T hN']

end Work.OddBound.indexTransfer
