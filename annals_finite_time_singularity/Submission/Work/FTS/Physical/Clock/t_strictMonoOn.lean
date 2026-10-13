/-
# `Work.FTS.Physical.Clock.t_strictMonoOn` — the clock `t(τ) = ∫₀^τ A` is strictly increasing

The amplitude `A` of the dynamic rescaling is strictly positive in fake time (`PhysClock.hApos`:
`0 < A τ` for `τ ≥ 0`), and the physical time is its primitive, `t(τ) = ∫₀^τ A(s) ds`
(`PhysClock.t`).  Hence for `0 ≤ a < b`,

  `t(b) - t(a) = ∫_a^b A(s) ds > 0`,

because the integrand is continuous and strictly positive on `[a,b]` (every `s ∈ [a,b]` satisfies
`s ≥ a ≥ 0`).  This is `intervalIntegral.intervalIntegral_pos_of_pos_on`, applied to the identity
`∫₀^b = ∫₀^a + ∫_a^b` (`intervalIntegral.integral_add_adjacent_intervals`).

Consequently `t` is injective on the fake-time half-line: the fake time is recovered from the
physical time, which is what makes the inverse clock `τ(t)` of the reconstruction well defined.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set MeasureTheory
open scoped Interval

namespace Work.FTS.Physical.Clock

/-- **The clock is strictly increasing in fake time.**  For `0 ≤ a < b` one has
`t a < t b`: the increment is `∫_a^b A > 0` since `A > 0` on the fake-time half-line. -/
theorem t_strictMonoOn (C : Work.FTS.Physical.PhysClock) : StrictMonoOn C.t (Set.Ici 0) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha
  -- `A` is continuous on `[a,b]`, hence interval integrable there
  have hint : IntervalIntegrable C.A volume a b :=
    (C.hAcont.mono fun x hx => le_trans ha0 hx.1).intervalIntegrable_of_Icc hab.le
  -- the integral of the (strictly positive, continuous) amplitude over `[a,b]` is positive
  have hpos : 0 < ∫ s in a..b, C.A s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hint
      (fun x hx => C.hApos x (le_trans ha0 hx.1.le)) hab
  -- additivity of the interval integral splits `t b = t a + ∫_a^b A`
  have hsplit : C.t b = C.t a + ∫ s in a..b, C.A s := by
    rw [Work.FTS.Physical.PhysClock.t, Work.FTS.Physical.PhysClock.t,
      ← intervalIntegral.integral_add_adjacent_intervals
        ((C.hAcont.mono fun x hx => hx.1).intervalIntegrable_of_Icc ha0) hint]
  linarith

end Work.FTS.Physical.Clock
