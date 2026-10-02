import Submission.Work.Landing.Land.Landing
import Submission.Work.Landing.Caratheodory.landsAt_of_extension

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The existence half of the landing theorem, from the Carathéodory input

`Submission/Work/Landing/Caratheodory/landsAt_of_extension` proves that if the inverse Böttcher
coordinate extends continuously to the unit circle (`Work.Landing.InverseBottcherExtends`), then
every dynamic ray lands (at the corresponding point of the extension).  Here that is combined with
the classification half of `Landing/Land/Landing.lean`:

* `Work.Landing.PeriodicRaysLand_of_extension` : **every periodic ray lands**;
* `Work.Landing.exists_landsAt_repelling_or_parabolic` : **Milnor 18.10**, existence and
  classification together, for odd periods.

The two classical ingredients are the extension input (local connectivity of the Julia set, i.e.
Böttcher's theorem extended to the boundary) and the Böttcher homeomorphism input
(`IsDynBottcherHomeo`); both are isolated as hypotheses and are the standard contents of the
Böttcher/landing theory of the sibling areas.
-/

noncomputable section

open Classical

namespace Work.Landing

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet)

variable {c : ℂ} {φ : ℂ → ℂ} {θ : ℝ} {z : ℂ} {k : ℕ}

/-- **Every periodic ray lands**, given the continuous extension of the inverse Böttcher
coordinate. -/
theorem PeriodicRaysLand_of_extension (h : IsDynBottcherHomeo c φ)
    (hext : InverseBottcherExtends c φ) : PeriodicRaysLand c := by
  obtain ⟨Ψ, hcont, hΨ⟩ := hext
  intro θ _
  exact ⟨Ψ (rayDirection θ), Work.Landing.Caratheodory.landsAt_of_extension h hcont hΨ θ⟩

/-- **Milnor 18.10, existence and classification.**  Every periodic ray lands, and if the period
`k` is odd the landing point is repelling or parabolic. -/
theorem exists_landsAt_repelling_or_parabolic (h : IsDynBottcherHomeo c φ)
    (hext : InverseBottcherExtends c φ) (hgeo : AttractingCyclesInner c)
    (hper : PeriodicAngle θ k) (hk : 0 < k) (hodd : Odd k) :
    ∃ z : ℂ, landsAt c θ z ∧ (IsRepelling c k z ∨ IsParabolic c k z) := by
  obtain ⟨Ψ, hcont, hΨ⟩ := hext
  have hland : landsAt c θ (Ψ (rayDirection θ)) :=
    Work.Landing.Caratheodory.landsAt_of_extension h hcont hΨ θ
  exact ⟨Ψ (rayDirection θ), hland,
    landsAt_repelling_or_parabolic hland hper hk hodd hgeo⟩

end Work.Landing
