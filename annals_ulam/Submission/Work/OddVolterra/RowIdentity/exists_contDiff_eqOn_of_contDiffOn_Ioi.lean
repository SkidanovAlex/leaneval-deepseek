import Mathlib
import Submission.Work.OddVolterra.RowIdentity.contDiff_mul_of_contDiffOn_of_tsupport_subset

namespace Work.OddVolterra.RowIdentity

open Metric Set

/-- The interval on which we have to reproduce `y` is
`(μ - R, μ + R)` with `μ = (c+d)/2` and `R = (d-c)/2 + c/4`; its left endpoint is
`μ - R = 3c/4 > 0`, so it sits strictly inside `Ioi 0` where `y` is smooth.

We therefore multiply `y` by a smooth bump function whose support is a slightly
larger ball around `μ` still contained in `Ioi 0`, and which equals `1` on the
closed ball of radius `R`. The product is globally smooth by
`contDiff_mul_of_contDiffOn_of_tsupport_subset`. -/
theorem exists_contDiff_eqOn_of_contDiffOn_Ioi {c d : ℝ} (hcd : c < d) (hc : 0 < c)
    {y : ℝ → ℝ} (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0)) :
    ∃ ν : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ν ∧
      ∀ t : ℝ, |t - (c + d) / 2| < (d - c) / 2 + c / 4 → ν t = y t := by
  set μ : ℝ := (c + d) / 2 with hμ
  set R : ℝ := (d - c) / 2 + c / 4 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hμR : R < μ := by rw [hR, hμ]; linarith
  -- A slightly larger radius whose ball is still contained in `Ioi 0`.
  set rOut : ℝ := (R + μ) / 2 with hrOut
  have hR_lt_rOut : R < rOut := by rw [hrOut]; linarith
  have hrOut_lt_μ : rOut < μ := by rw [hrOut]; linarith
  let f : ContDiffBump μ := ⟨R, rOut, hRpos, hR_lt_rOut⟩
  -- Its topological support is the closed ball of radius `rOut`, contained in `Ioi 0`.
  have hsupp : tsupport f ⊆ Set.Ioi 0 := by
    intro t ht
    rw [ContDiffBump.tsupport_eq, mem_closedBall, Real.dist_eq] at ht
    have h1 : -rOut ≤ t - μ := (abs_le.mp ht).1
    show 0 < t
    linarith
  refine ⟨fun t => f t * y t, ?_, ?_⟩
  · exact contDiff_mul_of_contDiffOn_of_tsupport_subset f.contDiff isOpen_Ioi hy hsupp
  · intro t ht
    have hft : f t = 1 := by
      apply f.one_of_mem_closedBall
      rw [mem_closedBall, Real.dist_eq]
      exact le_of_lt ht
    show f t * y t = y t
    rw [hft, one_mul]

end Work.OddVolterra.RowIdentity
