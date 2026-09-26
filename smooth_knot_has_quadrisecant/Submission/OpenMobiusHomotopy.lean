import Mathlib
import Submission.SecantModel
import Submission.Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract

open ContinuousMap
open unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# The open Möbius band is homotopy equivalent to its core circle

`OpenMobiusCoreRetract` (`openMobiusCoreRetract`,
`Submission/SecantModel.lean`) is the deformation retraction of the open
Möbius band of knot secants onto its core circle (antipodal pairs, the
image of `coreFactor : AddCircle halfPeriod → OpenMobius`,
`Submission/Pi1Mobius.lean`), obtained by transporting the chord-slide
retraction of the model Möbius band through the homeomorphism
`openMobiusModelHomeo : OpenMobius ≃ₜ MobiusModel`.

With the generic commons lemma
`Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract`
(`Submission/Commons/Topology/Homotopy/`) — exactly as in
`Submission/MobiusHomotopy.lean` for the model side — that deformation
retraction becomes a *homotopy equivalence*:

    OpenMobius ≃ₕ {c : OpenMobius // c ∈ Set.range coreFactor}

This is the `OpenMobius`-side certificate needed by the `π₁(OpenMobius) ≅ ℤ`
assembly (Layer C): the right-hand side is the core circle, which is
homeomorphic to `Circle` through `coreFactor_homeo` /
`coreRangeCircle` (`Submission/Pi1Mobius.lean`), and the fundamental group
of the circle is `ℤ` (fleet commons lemma
`Commons.AlgebraicTopology.FundamentalGroup.pi1_circle_eq_int`).
-/

/-- **The open Möbius band is homotopy equivalent to its core circle** (the
antipodal pairs `range coreFactor`). -/
lemma openMobius_homotopyEquiv_core :
    Nonempty (OpenMobius ≃ₕ {c : OpenMobius // c ∈ Set.range coreFactor}) := by
  rcases openMobiusCoreRetract with ⟨ρ, hcont, h0, h1, hfix_core⟩
  have h := Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract
    (X := OpenMobius)
    (C := {c : OpenMobius | c ∈ Set.range coreFactor})
    (ρ := ρ)
    hcont
    (fun c : OpenMobius => h0 c)
    (fun c : OpenMobius => h1 c)
    (by
      intro c hc t
      rcases hc with ⟨x, hx⟩
      rw [← hx]
      exact hfix_core x t)
  exact h

end LeanEval.KnotTheory.Quadrisecant
