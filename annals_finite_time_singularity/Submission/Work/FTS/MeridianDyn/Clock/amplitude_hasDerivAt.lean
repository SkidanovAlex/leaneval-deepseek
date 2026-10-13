import Mathlib.Analysis.Calculus.Deriv.Inv
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

open Work.FTS.Physical (clockInv clockInv_nonneg clockInv_hasDerivAt)

/-- **The derivative of the reciprocal amplitude `(A ∘ clockInv)⁻¹`.**

The amplitude `A` of the dynamic rescaling solves `A' = -(1+μ)A` in fake time, and the extended
inverse clock `clockInv C` is differentiable on `(0,T)` with derivative `(C.A (clockInv C t))⁻¹`.
Composing (`HasDerivAt.comp`), the chain rule gives

  `d/dt (A(τ(t))) = (-(1+μ(τ(t)))·A(τ(t)))·(C.A(τ(t)))⁻¹`,

and the reciprocal rule (`HasDerivAt.inv`, legitimate because `A(τ(t)) > 0`) turns this into the
stated derivative

  `d/dt (A(τ(t)))⁻¹ = (1+μ(τ(t)))·(C.A(τ(t)))⁻¹·(A(τ(t)))⁻¹`,

since `-(f')/A² = (1+μ)·(C.A)⁻¹·A/A²`.  Note that the `C.A` factor comes from the derivative of
the clock, whereas the `A`-factor and `μ` come from the amplitude equation: the two functions
`A` and `C.A` need not coincide for the identity to hold. -/
theorem amplitude_hasDerivAt {A : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock} {t : ℝ}
    (hAd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt A (-(1 + C.mu τ) * A τ) τ)
    (hApos : 0 < A (Work.FTS.Physical.clockInv C t))
    (ht : t ∈ Set.Ioo 0 C.T) :
    HasDerivAt (fun s => (A (Work.FTS.Physical.clockInv C s))⁻¹)
      ((1 + C.mu (Work.FTS.Physical.clockInv C t))
        * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        * (A (Work.FTS.Physical.clockInv C t))⁻¹) t := by
  have hτ : 0 ≤ clockInv C t := clockInv_nonneg C ⟨ht.1.le, ht.2⟩
  have hclock : HasDerivAt (clockInv C) ((C.A (clockInv C t))⁻¹) t := clockInv_hasDerivAt C ht
  have hA : HasDerivAt A (-(1 + C.mu (clockInv C t)) * A (clockInv C t)) (clockInv C t) :=
    hAd (clockInv C t) hτ
  -- chain rule: differentiate `A ∘ clockInv`
  have hcomp : HasDerivAt (fun s => A (clockInv C s))
      ((-(1 + C.mu (clockInv C t)) * A (clockInv C t)) * (C.A (clockInv C t))⁻¹) t :=
    hA.comp t hclock
  -- reciprocal rule, then collapse to the stated derivative
  refine (hcomp.inv (ne_of_gt hApos)).congr_deriv ?_
  field_simp

end Work.FTS.MeridianDyn.Clock
