import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.summable_coordError

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Exist

open Work.FatouCoord

/-- **The Abel equation for the Fatou coordinate in the chart.**  For `Re w` large enough
the series of defects along the orbit of `w` under `wMap f` converges, and the Fatou coordinate
`fatouCoordW f (1 - a) w = w - (1 - a) log w + ∑ coordError` satisfies the Abel equation

`fatouCoordW (wMap f w) = fatouCoordW w + 1`.

The proof is a telescoping argument: shifting the index in the sum of defects picks up exactly
the defect at `w`, which is `approxCoord (wMap f w) - approxCoord w - 1`. -/
theorem fatouCoordW_abel {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ ∀ w : ℂ, N < w.re →
      fatouCoordW f (1 - a) (wMap f w) = fatouCoordW f (1 - a) w + 1 := by
  obtain ⟨N, hNpos, hrN, hsum⟩ := Work.FatouCoord.Estimate.summable_coordError hb
  refine ⟨N, hNpos, hrN, fun w hw => ?_⟩
  -- the defects along the orbit of `w` are summable
  have hS : Summable (fun k : ℕ => coordError f (1 - a) ((wMap f)^[k] w)) :=
    Summable.of_norm (hsum w hw)
  -- unfold both occurrences of the Fatou coordinate
  rw [fatouCoordW_eq, fatouCoordW_eq]
  -- the orbit of `wMap f w` is the orbit of `w` shifted by one
  have hterm : ∀ k : ℕ,
      coordError f (1 - a) ((wMap f)^[k] (wMap f w))
        = coordError f (1 - a) ((wMap f)^[k+1] w) := by
    intro k
    rw [Function.iterate_succ_apply]
  rw [tsum_congr hterm]
  -- shifting the index of a summable series subtracts the first term
  have hT : (∑' k : ℕ, coordError f (1 - a) ((wMap f)^[k+1] w))
      = (∑' k : ℕ, coordError f (1 - a) ((wMap f)^[k] w)) - coordError f (1 - a) w := by
    rw [eq_sub_iff_add_eq]
    have h := hS.sum_add_tsum_nat_add 1
    simpa [Finset.sum_range_one, add_comm] using h
  rw [hT, coordError_apply]
  ring

end Work.FatouCoord.Exist
