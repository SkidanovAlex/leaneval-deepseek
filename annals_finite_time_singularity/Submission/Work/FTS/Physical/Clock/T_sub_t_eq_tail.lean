/-
# `Work.FTS.Physical.Clock.T_sub_t_eq_tail` — the tail identity `T - t(τ) = ∫_τ^∞ A`

The blow-up time is `T = ∫_0^∞ A` and the physical time is `t(τ) = ∫_0^τ A`.  Splitting the
half-line `[0,∞) = [0,τ] ∪ [τ,∞)` at a fake time `τ ≥ 0` gives the **tail identity**

  `T - t(τ) = ∫_{[τ,∞)} A s ds`  for `0 ≤ τ`  (`Work.FTS.Physical.Clock.T_sub_t_eq_tail`),

the analytic form of "the physical time left to blow-up is the fake-time tail of the amplitude".
It is the identity from which the quantitative comparison `A τ ≍ T - t(τ)` is read off
(`Work.FTS.Physical.Clock.tail_le_two_mul`), and it is the input of the `c/(T-t)` vorticity
lower bound of the reconstruction.

The proof is the interval-integral splitting lemma `intervalIntegral.integral_Ici_sub_Ici'`
applied to the integrability of `A` on `[0,∞)` (proved in
`Work.FTS.Physical.Clock.integrableOn_A`), together with the definitions of `T` and `t`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Clock.integrableOn_A

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped Topology

namespace Work.FTS.Physical.Clock

/-- **The tail identity** `T - t(τ) = ∫_{[τ,∞)} A`: the physical time that is left until the
blow-up is exactly the fake-time integral of the amplitude from `τ` on. -/
theorem T_sub_t_eq_tail (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) : C.T - C.t τ = ∫ s in Set.Ici τ, C.A s := by
  -- `A` is integrable on `[0,∞)`, hence on the sub-half-line `[τ,∞)`.
  have h0 : IntegrableOn C.A (Set.Ici 0) := integrableOn_A C
  have hτi : IntegrableOn C.A (Set.Ici τ) := h0.mono_set (Set.Ici_subset_Ici.2 hτ)
  -- splitting `[0,∞) = [0,τ] ∪ [τ,∞)` at `τ`:
  have hsplit := intervalIntegral.integral_Ici_sub_Ici' (f := C.A) (a := 0) (b := τ) h0 hτi
  -- unfold `T = ∫_0^∞ A` and `t τ = ∫_0^τ A`
  simp only [Work.FTS.Physical.PhysClock.T, Work.FTS.Physical.PhysClock.t]
  linarith [hsplit]

end Work.FTS.Physical.Clock
