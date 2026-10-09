import Mathlib
import Submission.Work.SSGRoute.PTW.RegularRep
import Submission.Work.SSGRoute.PTW.AvgOpNeZero
import Submission.Work.SSGRoute.PTW.avgOp_regRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTW

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal

/-- `avgOp ξ` is a compact operator.  Route: the integrand
`g ↦ rankOneOp (regRep g ξ) (regRep g ξ)` is (a.e.) compact-valued (`rankOneIsCompact` composed
with `continuous_rankOneOp_regRep`), the set `{T | IsCompactOperator T}` is convex (it is a linear
subspace) and closed (`isClosed_setOfPred_isCompactOperator` / alias
`isClosed_setOf_isCompactOperator`), so `Convex.integral_mem`
(`Mathlib/Analysis/Convex/Integral.lean`) with `[IsProbabilityMeasure μ]` and
`integrable_rankOneOp_regRep` (`AvgOpNeZero.lean`) gives the conclusion, `avgOp` unfolding
definitionally. -/
theorem avgOp_isCompact {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : MeasureTheory.Measure Q}
    [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsLocallyFiniteMeasure μ] [MeasureTheory.Measure.InnerRegularCompactLTTop μ]
    (ξ : MeasureTheory.Lp ℂ 2 μ) :
    IsCompactOperator (Work.SSGRoute.PTW.avgOp (μ := μ) ξ) := by
  -- the set of compact operators is a linear subspace, hence convex
  have hconv : Convex ℝ {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ | IsCompactOperator T} := by
    have h : Convex ℝ
        (((compactOperator (RingHom.id ℂ) (Lp ℂ 2 μ) (Lp ℂ 2 μ)).restrictScalars ℝ) :
          Set (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) := Submodule.convex _
    rwa [Submodule.coe_restrictScalars] at h
  -- and it is closed
  have hclosed : IsClosed {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ | IsCompactOperator T} :=
    isClosed_setOfPred_isCompactOperator
  -- the integrand takes values in it
  have hmem : ∀ᵐ g ∂μ,
      rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) ∈
        {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ | IsCompactOperator T} :=
    Eventually.of_forall fun g => by
      show IsCompactOperator
        (fun η : Lp ℂ 2 μ => inner ℂ (regRep (μ := μ) g ξ) η • regRep (μ := μ) g ξ)
      exact rankOneIsCompact _ _
  have hint : Integrable (fun g : Q =>
      rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ)) μ :=
    integrable_rankOneOp_regRep (μ := μ) ξ
  have h := hconv.integral_mem hclosed hmem hint
  rwa [avgOp]

end Work.SSGRoute.PTW
