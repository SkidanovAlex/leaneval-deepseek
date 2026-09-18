import Mathlib.NumberTheory.WellApproximable
import Submission.Helpers
import Submission.Commons.NumberTheory.DuffinSchaeffer.km_full_conv
import Submission.Commons.NumberTheory.DuffinSchaeffer.km_full_hard_of_not_tendsto
import Submission.Commons.NumberTheory.DuffinSchaeffer.volume_eq_one_of_positive_measure
import Submission.Work.NumberTheory.DuffinSchaeffer.km_hard_positive

/-!
# The Duffin–Schaeffer theorem, Mathlib-shaped — ALREADY PROVED

This module is the single handle on the finished Koukoulopoulos–Maynard theorem.
It was proved by the `duffin_schaeffer` fundmath3 run on 2026-09-18 and is carried
into this workspace whole: the statement below is sorry-free and its import
closure (135 modules, all present in this seed) is sorry-free, with

    #print axioms Submission.duffin_schaeffer_mathlib
    ⟹ [propext, Classical.choice, Quot.sound]

**Do not re-prove it, and do not continue the 28-sorry research programme under
`Submission/DS/` that was aimed at it** (see `Submission/DS/GAPMAP.md`, whose
sections (A)–(E) are now obsolete as a route to `theorem_1`).  The remaining work
in THIS problem is transport, not analysis — see `HANDOFF.md`.

The radii are Mathlib's: `δ : ℕ → ℝ` and `addWellApproximable UnitAddCircle δ`.
The challenge's `𝒜 ψ` lives in `ℝ` and is indexed by `ℕ+`; `Submission/DS/CircleBridge.lean`
already defines the translation `radSeq ψ : ℕ → ℝ` (`radSeq ψ n = ψ n / n`), and
`CircAlign.lean` / `CircVol.lean` already relate `𝒜`-style sets to
`approxAddOrderOf` sets on `AddCircle (1 : ℝ)`, sorry-free.
-/

open MeasureTheory

namespace Submission

/-- **Duffin–Schaeffer conjecture** (Koukoulopoulos–Maynard, Ann. of Math. 192 (2020)),
in Mathlib's formulation.  Proved; see the module docstring. -/
theorem duffin_schaeffer_mathlib (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) :
    volume (addWellApproximable UnitAddCircle δ) = 1 ↔
      ¬ Summable fun n : ℕ => n.totient * δ n := by
  constructor
  · intro hvol hs
    have h0 := Commons.NumberTheory.DuffinSchaeffer.km_full_conv δ hδ hs
    rw [hvol] at h0
    exact one_ne_zero h0
  · intro h
    by_cases hδt : Filter.Tendsto δ Filter.atTop (nhds 0)
    · exact Commons.NumberTheory.DuffinSchaeffer.volume_eq_one_of_positive_measure δ hδt
        (Commons.NumberTheory.DuffinSchaeffer.km_hard_positive δ hδ hδt h)
    · exact Commons.NumberTheory.DuffinSchaeffer.km_full_hard_of_not_tendsto δ hδ hδt

end Submission
