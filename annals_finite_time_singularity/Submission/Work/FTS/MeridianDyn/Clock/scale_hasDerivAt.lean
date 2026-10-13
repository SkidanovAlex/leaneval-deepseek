import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.Physical.Clock.clockInv
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Clock

/-- **The derivative of a scale function along the physical clock.**

If `B` solves the (fake-time) linear ODE `B' = -(1 - μ) · B` on the nonnegative half-line, then the
composition `s ↦ B(τ(s))` of `B` with the inverse clock `τ = clockInv C` is differentiable at every
physical time `t ∈ (0,T)`, with derivative

  `-(1 - μ(τ(t))) · A(τ(t))⁻¹ · B(τ(t))`.

This is the chain rule: `d/ds B(τ(s)) = B'(τ(s))·τ'(s)`, the derivative of the clock being
`A(τ(s))⁻¹` (`Work.FTS.Physical.clockInv_hasDerivAt`).  The hypothesis `hBd` is only available on
`[0,∞)` in fake time, which is exactly where `τ(t)` lives for `t ∈ (0,T)`. -/
theorem scale_hasDerivAt {B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock} {t : ℝ}
    (hBd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt B (-(1 - C.mu τ) * B τ) τ)
    (ht : t ∈ Set.Ioo 0 C.T) :
    HasDerivAt (fun s => B (Work.FTS.Physical.clockInv C s))
      (-(1 - C.mu (Work.FTS.Physical.clockInv C t))
        * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        * B (Work.FTS.Physical.clockInv C t)) t := by
  have hτ : 0 ≤ Work.FTS.Physical.clockInv C t :=
    Work.FTS.Physical.clockInv_nonneg C ⟨ht.1.le, ht.2⟩
  have hB : HasDerivAt B
      (-(1 - C.mu (Work.FTS.Physical.clockInv C t))
        * B (Work.FTS.Physical.clockInv C t)) (Work.FTS.Physical.clockInv C t) :=
    hBd (Work.FTS.Physical.clockInv C t) hτ
  have hclock : HasDerivAt (Work.FTS.Physical.clockInv C)
      (C.A (Work.FTS.Physical.clockInv C t))⁻¹ t :=
    Work.FTS.Physical.clockInv_hasDerivAt C ht
  have hcomp := hB.comp t hclock
  have heq : (-(1 - C.mu (Work.FTS.Physical.clockInv C t))
          * B (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        = -(1 - C.mu (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
          * B (Work.FTS.Physical.clockInv C t) := by
    ring
  rw [heq] at hcomp
  exact hcomp

end Work.FTS.MeridianDyn.Clock
