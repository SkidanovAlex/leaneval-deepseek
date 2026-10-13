/-
# The time derivative of the (negated) physical vorticity through the clock

`Work.FTS.FireFix.Clauses.Support.timeDeriv_physOmega_eq`: for every `x : ℝ³` and every physical
time `t ∈ [0, C.T)`,

  `∂ₜ(−physOmega α A B g C)(x,t) = − (C.A (τ(t)))⁻¹ • ∂_τ (physVort α A B g)(x, τ(t))`,

with `τ(t) = clockInv C t`.

## The mathematical point

`physOmega α A B g C x t = physVort α A B g x (clockInv C t)` is the profile field at fake time
`τ = clockInv C t`; the integer factor in front of the field (`(A τ)⁻¹` inside `physVort`) is part
of `physVort`, so the identity is *purely* the chain rule for the composite
`s ↦ physVort α A B g x (clockInv C s)`:

  `d/ds [physVort x (τ(s))] = τ'(s) • ∂_τ physVort x (τ(s))`  at `s = t`,

evaluated with the two inputs

* `τ' = (C.A (clockInv C t))⁻¹` — `Work.FTS.Physical.clockInv_hasDerivAt` for `t ∈ (0, T)` and
  `Work.FTS.Physical.clockInv_hasDerivAt_zero` for `t = 0` (this is what the tangent extension of
  the inverse clock at `0` is for);
* `∂_τ physVort α A B g x (clockInv C t)` — the strip statement
  `Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound`, which is *two-sided* at `τ = 0` thanks
  to the `C¹`-in-`(z,τ)` clause `hcont` of `RegPkg'`.

`FiniteTimeSingularity.timeDeriv` is by definition the `deriv` of the time slice, so the conclusion
is the `.deriv` of the `HasDerivAt` obtained from `HasDerivAt.scomp` plus `neg`.  This is the exact
content of the chain rule already computed inside the sibling
`Work.FTS.FireFix.Clauses.physOmega_hasDerivWithinAt`; here it is returned in the *two-sided*
`deriv` form.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.FireFix.PhysData
import Submission.Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound
import Submission.Work.FTS.Physical.Clock.clockInv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.Support

theorem timeDeriv_physOmega_eq {α : ℝ} (hα : 0 < α)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' α S A B g)
    (x : EuclideanSpace ℝ (Fin 3)) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) C.T) :
    FiniteTimeSingularity.timeDeriv
        (fun y s => - Work.FTS.Physical.physOmega α A B g C y s) x t
      = - ((C.A (Work.FTS.Physical.clockInv C t))⁻¹ •
            FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x
              (Work.FTS.Physical.clockInv C t)) := by
  -- the fake-time coordinate of `t` is nonnegative, so it lies in the strip `[0, τ(t)+1]`
  have hpos : 0 ≤ Work.FTS.Physical.clockInv C t := Work.FTS.Physical.clockInv_nonneg C ht
  obtain ⟨hder, _⟩ :=
    Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound (α := α)
      (S := Work.FTS.Physical.clockInv C t + 1) (A := A) (B := B) (g := g)
      (hreg _ (by linarith : (0 : ℝ) < Work.FTS.Physical.clockInv C t + 1))
  have hv := hder x _ ⟨hpos, by linarith⟩
  -- the extended inverse clock is differentiable at every `t ∈ [0, C.T)`, including `t = 0`
  have hc : HasDerivAt (Work.FTS.Physical.clockInv C)
      ((C.A (Work.FTS.Physical.clockInv C t))⁻¹) t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      simpa using Work.FTS.Physical.clockInv_hasDerivAt_zero C
    · exact Work.FTS.Physical.clockInv_hasDerivAt C ⟨h, ht.2⟩
  -- chain rule, then negation
  have hgs : HasDerivAt
      (fun s : ℝ => Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s))
      ((C.A (Work.FTS.Physical.clockInv C t))⁻¹ •
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x
          (Work.FTS.Physical.clockInv C t)) t := by
    simpa [Function.comp_def] using hv.scomp t hc
  have hneg := hgs.neg
  -- `physOmega`/`timeDeriv` unfold definitionally to the composite above
  change deriv (fun s : ℝ =>
      - (Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s))) t
    = - ((C.A (Work.FTS.Physical.clockInv C t))⁻¹ •
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x
          (Work.FTS.Physical.clockInv C t))
  exact hneg.deriv

end Work.FTS.FireFix.Clauses.Support
