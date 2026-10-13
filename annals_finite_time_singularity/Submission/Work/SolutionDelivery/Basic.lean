/-
# `Work.SolutionDelivery.Basic` — the derived fields of the input package

The fields of `ConstructedSolution` that are *not* assumptions but consequences of the other
chapters' material, and whose proofs need modules above `Defs`:

* `coreU` — the core joint `C^{1,α}` regularity of the velocity, a restriction of the LWP chapter's
  maximal-solution strip regularity `Work.LWP.MaximalSolution.spacetime`
  (`Holder/isContDiffHolderOn_coreRegion_Icc`);
* `ω₀_int`, `ω₀_supp`, `ω₀_bdd`, `ω₀_holder` — the elementary properties of the concrete `St1`
  cut-off datum `ω₀ = χ(ρ/L)·ωS` (`DatumCut`, `DatumCut/cutDatum_holder`);
* `ω₀_div`, `ω₀_odd` — the two `Cyl`/Biot–Savart dictionary clauses (fields of
  `ConstructedSolution`, restated here for convenience).
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.Defs
import Submission.Work.SolutionDelivery.DatumCut
import Submission.Work.SolutionDelivery.DatumCut.cutDatum_holder
import Submission.Work.SolutionDelivery.Holder.isContDiffHolderOn_coreRegion_Icc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

namespace ConstructedSolution

variable {α : NNReal} (C : ConstructedSolution α)

/-- **The core regularity of the velocity**: the field `AssemblyInputs.core` with its radius
pinned — a restriction of the LWP chapter's strip regularity `C.hmax.spacetime`. -/
theorem coreU : ∀ S ∈ Set.Ioo 0 C.T,
    IsContDiffHolderOn ℝ α C.u.uncurry
      (Work.StabilityFar.coreRegion (Work.StabilityFar.st4Radius C.R + 1) ×ˢ Set.Icc 0 S) :=
  fun S hS => Holder.isContDiffHolderOn_coreRegion_Icc
    (ρ := Work.StabilityFar.st4Radius C.R + 1) (S := S)
    (by simp only [Work.StabilityFar.st4Radius]; linarith [C.hR]) hS.1 (C.hmax.spacetime S hS)

/-- The cut-off datum is integrable. -/
theorem ω₀_int : Integrable C.ω₀ volume :=
  cutDatum_integrable C.hL C.ωS_meas C.ωS_bdd

/-- The cut-off datum is supported in `B(0,2L)`. -/
theorem ω₀_supp : ∀ y : R3, C.ω₀ y ≠ 0 → y ∈ Metric.closedBall 0 (2 * C.L) :=
  cutDatum_support C.hL

/-- The cut-off datum is bounded by `M`. -/
theorem ω₀_bdd : ∀ y : R3, ‖C.ω₀ y‖ ≤ C.M := cutDatum_bdd C.ωS_bdd

/-- The cut-off datum is `α`-Hölder (needs `α ≤ 1`, the range of the construction). -/
theorem ω₀_holder (hα : 0 < α) (hα1 : α ≤ 1) : Holder α C.ω₀ :=
  DatumCut.cutDatum_holder C.hL hα hα1 C.ωS_cdh

/-- The cut-off datum is divergence-free (the `Cyl` dictionary clause). -/
theorem ω₀_div : ∀ x : R3, div C.ω₀ x = 0 := C.ωS_div

/-- The datum `u₀ = BS ω₀` is odd (the `Cyl` parity dictionary clause). -/
theorem ω₀_odd : IsOdd (Work.LWP.biotSavart C.ω₀) := C.ωS_odd

end ConstructedSolution

end Work.SolutionDelivery
