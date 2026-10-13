import Mathlib
import Submission.Work.WilC5.SatSetup

namespace Work.WilC5

/-- `SatIdx κ` is the (well-ordered) type of ordinals below `(Order.succ (Order.succ (κ + ℵ₀))).ord`,
the initial ordinal of the second successor cardinal of `κ + ℵ₀`. That cardinal is infinite, hence so
is its initial ordinal, which is therefore a limit ordinal; the type of smaller ordinals then has no
greatest element. Concretely we invoke `Cardinal.noMaxOrder`, which says that `c.ord.ToType` has no
maximal element as soon as `ℵ₀ ≤ c`. -/
theorem SatIdxNoMax (κ : Cardinal.{0}) : NoMaxOrder (SatIdx κ) := by
  unfold SatIdx
  refine Cardinal.noMaxOrder (c := Order.succ (Order.succ (κ + Cardinal.aleph0))) ?_
  calc Cardinal.aleph0 ≤ κ + Cardinal.aleph0 :=
        Cardinal.aleph0_le_add_iff.mpr (Or.inr le_rfl)
    _ ≤ Order.succ (κ + Cardinal.aleph0) := Order.le_succ _
    _ ≤ Order.succ (Order.succ (κ + Cardinal.aleph0)) := Order.le_succ _

end Work.WilC5
