import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/RawSliceL12Zero.lean` — OPEN SUB-LEAF of L-A (REVIEW fix F6)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling_REVIEW.md` F6).  The raw slice's zero mode
vanishes along a regular ε-solution; L-A (`rawE6_ineq`) needs it for `|c(Jg)| ≲ ε|g|₅`.
Route: `StrongEps.L12_slice_eq_zero_of_hkMem` (PROVED; needs `hc1` = `hreg.1`, `SmoothOpen`/
`HkMem 4` of slices from `hreg.2`, a uniform `ℋ⁴` bound `B` of `epsRHSP` and `HkMem 4` of
`J_ε epsWP`) with `h0 := l12_zero_of_epsDatum hα hρ hd`.  The uniform `B` is the same regularity
issue as R2 (`rawE6_deriv`): if it cannot be produced from `EpsRegP`, return "missing hypothesis".
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false

/-- **OPEN SUB-LEAF (F6)** `L₁₂(slice g τ)(0) = 0` along a regular ε-solution. -/
theorem rawSlice_L12_zero {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (hρ : IsSmoothKernel ρ) (hα : α ∈ Ioc (0 : ℝ) 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hT : 0 < T) (hd : ∀ ε' : ℝ, 0 < ε' → EpsDatum α ρ ε' g₀)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g) (hreg : EpsRegP α ρ ε T g) :
    ∀ τ ∈ Icc 0 T, Work.Construction.L12 (slice g τ) 0 = 0 := by
  sorry

end Work.FTS.StrongEps.EpsE4Thr.E4R4
