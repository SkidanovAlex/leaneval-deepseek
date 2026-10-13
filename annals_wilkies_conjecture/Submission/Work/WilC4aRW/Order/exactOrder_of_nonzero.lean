import Mathlib
import Submission.Work.WilC4aRW.Defs

namespace Work.WilC4aRW.Order

open ClassicalComplexWPT Filter Topology
open scoped Topology

/-- The order of the last-variable slice of an analytic germ at the origin, as an element of
`ℕ∞`; it is `⊤` exactly when the slice vanishes identically near the origin. -/
theorem analyticOrderAt_lastSlice_ne_top {n : ℕ} {f : Ambient n → ℂ}
    (hne : ¬ (lastSlice f =ᶠ[nhds (0 : ℂ)] fun _ => 0)) :
    analyticOrderAt (lastSlice f) 0 ≠ ⊤ :=
  fun h => hne (analyticOrderAt_eq_top.mp h)

/-- A nonzero analytic germ in the last variable has a (finite) exact order in that variable. -/
theorem exactOrder_of_nonzero {n : ℕ} {f : ClassicalComplexWPT.Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hne : ¬ (ClassicalComplexWPT.lastSlice f =ᶠ[nhds (0 : ℂ)] fun _ => 0)) :
    ∃ d, ClassicalComplexWPT.ExactOrderInLastVariable f d := by
  refine ⟨(analyticOrderAt (lastSlice f) 0).toNat, ?_⟩
  rw [exactOrderInLastVariable_iff_analyticOrderAt hf]
  exact (ENat.natCast_toNat (analyticOrderAt_lastSlice_ne_top hne)).symm

end Work.WilC4aRW.Order
