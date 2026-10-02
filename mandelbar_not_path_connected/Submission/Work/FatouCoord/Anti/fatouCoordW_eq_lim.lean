import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.summable_coordError

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Fatou coordinate is the limit of the approximate coordinates

For a parabolic germ satisfying the quantitative hypotheses `ParabolicBounds`, the explicit Fatou
coordinate in the chart `w = -1/z`,

`fatouCoordW f (1 - a) x = approxCoord (1 - a) x + ∑' k, coordError f (1 - a) ((wMap f)^[k] x)`,

is the limit of the approximate coordinates along the orbit: for `Re x` large enough,

`approxCoord (1 - a) ((wMap f)^[n] x) - n → fatouCoordW f (1 - a) x`.

The proof is the telescoping identity

`approxCoord c ((wMap f)^[n] x) - n = approxCoord c x + ∑_{k<n} coordError f c ((wMap f)^[k] x)`,

which follows from `coordError f c w = approxCoord c (wMap f w) - approxCoord c w - 1`, combined
with the summability of the defects along the orbit (`Estimate.summable_coordError`).
-/

namespace Work.FatouCoord.Anti

open Work.FatouCoord
open scoped Topology
open Filter

/-- **Telescoping identity.**  The `n`-th approximate coordinate along the orbit, corrected by
the translation count `n`, is the initial approximate coordinate plus the sum of the defects of
the approximate Abel equation along the first `n` steps of the orbit. -/
theorem approxCoord_iterate_sub (f : ℂ → ℂ) (c : ℂ) (x : ℂ) (n : ℕ) :
    approxCoord c ((wMap f)^[n] x) - (n : ℂ)
      = approxCoord c x + ∑ k ∈ Finset.range n, coordError f c ((wMap f)^[k] x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : approxCoord c ((wMap f)^[n] x)
        = approxCoord c x + (∑ k ∈ Finset.range n, coordError f c ((wMap f)^[k] x))
          + (n : ℂ) := by
      rw [← ih]
      ring
    rw [Function.iterate_succ_apply', Finset.sum_range_succ, coordError_apply, key]
    push_cast
    ring

/-- **The Fatou coordinate is the limit of the approximate coordinates along the orbit.**
This is the standard way of computing `fatouCoordW`: the partial sums of the defect series
converge to its sum, and the telescoping identity identifies the sequence
`approxCoord (1 - a) ((wMap f)^[n] x) - n` with those partial sums. -/
theorem fatouCoordW_eq_lim {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A') : ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ ∀ x : ℂ, N < x.re → Filter.Tendsto (fun n : ℕ => Work.FatouCoord.approxCoord (1 - a) ((Work.FatouCoord.wMap f)^[n] x) - (n : ℂ)) Filter.atTop (nhds (Work.FatouCoord.fatouCoordW f (1 - a) x)) := by
  obtain ⟨N, hNpos, hrN, hsum⟩ := Estimate.summable_coordError hb
  refine ⟨N, hNpos, hrN, fun x hx => ?_⟩
  -- the defects along the orbit of `x` are summable
  have hS : Summable (fun k : ℕ => coordError f (1 - a) ((wMap f)^[k] x)) :=
    Summable.of_norm (hsum x hx)
  -- partial sums converge to the sum of the series
  have hlim : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      coordError f (1 - a) ((wMap f)^[k] x)) atTop
      (nhds (∑' k : ℕ, coordError f (1 - a) ((wMap f)^[k] x))) :=
    hS.hasSum.tendsto_sum_nat
  have hlim' := hlim.const_add (approxCoord (1 - a) x)
  -- unfold the Fatou coordinate and identify the two sequences
  rw [fatouCoordW_eq]
  refine Tendsto.congr' (Eventually.of_forall fun n => ?_) hlim'
  exact (approxCoord_iterate_sub f (1 - a) x n).symm

end Work.FatouCoord.Anti
