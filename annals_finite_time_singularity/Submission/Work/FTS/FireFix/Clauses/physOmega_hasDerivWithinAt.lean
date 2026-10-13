/-
# The time-derivative clause of the (negated) physical vorticity

`Work.FTS.FireFix.Clauses.physOmega_hasDerivWithinAt`: the (negated) physical vorticity
`ω := −physOmega α A B g C` is, at every `x : ℝ³` and every physical time `t ∈ [0, C.T)`,
differentiable *within* the half-line `[t, ∞)` with derivative its own time derivative
`∂ₜω(x,t) = FiniteTimeSingularity.timeDeriv ω x t`.

## The mathematical point

`physOmega α A B g C x t = physVort α A B g x (clockInv C t)` is the composition of the profile
field at fake time `τ = clockInv C t` with the (tangent-extended) inverse clock.  The requested
derivative is the *two-sided* derivative `deriv` of the composite, not merely a one-sided one, so
two facts are needed:

* `clockInv C` is differentiable at **every** `t ∈ [0, C.T)`, including `t = 0`, with derivative
  `(C.A (clockInv C t))⁻¹`: this is the whole point of the tangent extension of the inverse clock
  (`Work.FTS.Physical.clockInv_hasDerivAt`, `Work.FTS.Physical.clockInv_hasDerivAt_zero`);
* `τ ↦ physVort α A B g x τ` is differentiable at `τ₀ = clockInv C t`.
  For `τ₀ > 0` this is the strip statement; for `τ₀ = 0` it is genuine two-sided information, and
  it is exactly what the `hcont` field of `RegPkg'` supplies: `(z,τ) ↦ g z θ τ` is `C¹` on
  `Ioi(-1) ×ˢ Ioo(-1)(S+1)` for every `θ ∈ Iθ`, i.e. on a **two-sided** neighbourhood of any
  negative-to-positive fake time near `0`.  Both facts are collected in the already proved
  `Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound` (the `RegPkg'` version of
  `Work.FTS.Regularity.physVort_hasDerivAt_and_bound`).

The proof is then the chain rule for `τ ↦ clockInv C t` applied at `τ`, plus the rewriting of
`physOmega`/`timeDeriv` by definitional unfolding, and it finishes with
`HasDerivAt.differentiableAt.hasDerivAt.hasDerivWithinAt` — the `deriv` in the statement is the
very two-sided derivative we have just computed.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.FireFix.PhysData
import Submission.Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.FireFix.Clauses

/-- **The time-derivative clause.**  For every `x : ℝ³` and every `t ∈ [0, C.T)`, the negated
physical vorticity `s ↦ −physOmega α A B g C x s` has, within `[t, ∞)`, the derivative equal to
its own time derivative `∂ₜ(−physOmega α A B g C)(x,t)`.

Both sides are the chain-rule value: the two-sided derivative of `τ ↦ physVort α A B g x τ` at
`τ = clockInv C t`, composed with the derivative `(C.A (clockInv C t))⁻¹` of the extended inverse
clock. -/
theorem physOmega_hasDerivWithinAt {α : ℝ} (hα : 0 < α)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ∀ x : EuclideanSpace ℝ (Fin 3), ∀ t ∈ Set.Ico (0 : ℝ) C.T,
      HasDerivWithinAt (fun s : ℝ => - (Work.FTS.Physical.physOmega α A B g C x s))
        (FiniteTimeSingularity.timeDeriv
          (fun y s => - (Work.FTS.Physical.physOmega α A B g C y s)) x t)
        (Set.Ici t) t := by
  intro x t ht
  -- the fake-time coordinate `τ₀ = clockInv C t` is nonnegative, hence lies in a strip `[0,S]`
  have hpos : 0 ≤ Work.FTS.Physical.clockInv C t := Work.FTS.Physical.clockInv_nonneg C ht
  obtain ⟨hder, _⟩ :=
    Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound
      (hreg _ (by linarith : 0 < Work.FTS.Physical.clockInv C t + 1))
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
  have hneg : HasDerivAt
      (fun s : ℝ => - (Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s)))
      (-((C.A (Work.FTS.Physical.clockInv C t))⁻¹ •
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x
          (Work.FTS.Physical.clockInv C t))) t :=
    hgs.neg
  -- `physOmega` and `timeDeriv` unfold definitionally to the composite above
  show HasDerivWithinAt
      (fun s : ℝ => - (Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s)))
      (deriv (fun s : ℝ => -
        (Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C s))) t)
      (Set.Ici t) t
  exact hneg.differentiableAt.hasDerivAt.hasDerivWithinAt

end Work.FTS.FireFix.Clauses
