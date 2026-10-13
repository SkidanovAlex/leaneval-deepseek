/-
# `Work.R1G.ModulatedInstance` — the modulated profile data is **inhabited**

Deliverable 1 of the G-route asks for "the modulated ProfileData (`g ≠ 0`)".  The delivered
`Work.ConstructionInstance.profileData_inhabited` has `g = 0`; this module supplies an inhabitant
whose perturbation is **visible in the open quadrant** and whose modulation is the affine
`λ̄(t) = 1 - t/2` of the delivered inhabitant (so that the rate is `κ = 1/2` and `EffRate` holds),
together with the derivation bundle `GDerivDataQd` of `Defs.lean`.

The `g`-equation is satisfied *by construction*: taking `Far := gEqResidual P (1/2) 0`, the
`g`-equation `GEquationStat P (1/2) 0 Far` holds by `gEquationStat_iff` — i.e. the `far-field term
is defined as the residual of the data at hand, which is exactly the sense in which the honest
interface "carries the deficit".

What this does **not** provide is `Far = 0`: the vanishing of the `g`-equation's far-field term at a
modulated datum is precisely the honest content of residual R1 (`NOTES.md` §5), and is not available
here any more than anywhere else.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.R1G.Defs
import Submission.Work.R1G.GEquation
import Submission.Work.R1G.gDerivDataQd_phi_zero
import Submission.Work.R1G.exists_profileData_g_visible

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.R1G

variable {α : NNReal}

/-- **The modulated profile data is inhabited.**  There is a `ModulatedData α` with
`κ = 1/2` and the zero stream function: the perturbation is nonzero in the open quadrant
(`exists_profileData_g_visible`), the modulation is affine so that the rate is `1/2`, and the
`g`-equation holds with `Far` the residual of the data. -/
theorem modulatedData_exists (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    ∃ D : ModulatedData α, D.κ = 1 / 2 ∧ D.Φ = (fun _ _ : ℝ => 0) := by
  obtain ⟨P, hgnz, hlam⟩ := exists_profileData_g_visible hα hα13
  refine ⟨{ P := P, hgnz := hgnz, κ := 1 / 2, hrate := ?_,
            Φ := fun _ _ => 0, Far := gEqResidual P (1 / 2) (fun _ _ => 0),
            hFar := ?_, hD := gDerivDataQd_phi_zero P }, rfl, rfl⟩
  · intro t _
    rw [hlam]
    simpa using ((hasDerivAt_id t).div_const 2).const_sub 1
  · rw [gEquationStat_iff]
    intro z θ _
    rfl

/-- **The `g`-equation's residual is the far-field term of the inhabiting datum** — the sense in
which the interface "carries the deficit". -/
theorem modulatedData_gEqResidual_eq_far (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    ∃ D : ModulatedData α, D.κ = 1 / 2 ∧
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        gEqResidual D.P D.κ D.Φ z θ = D.Far z θ) := by
  obtain ⟨D, hκ, -⟩ := modulatedData_exists hα hα13
  exact ⟨D, hκ, fun z θ hzθ => D.gEqResidual_eq_far z θ hzθ⟩

end Work.R1G
