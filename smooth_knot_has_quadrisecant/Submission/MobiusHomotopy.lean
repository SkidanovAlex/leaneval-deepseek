import Mathlib
import Submission.MobiusModel
import Submission.Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract

open ContinuousMap
open unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# The model Möbius band is homotopy equivalent to its core circle

With the deformation retraction `mobiusSlide` (`MobiusCoreRetract`,
`Submission/MobiusModel.lean`) in hand, the generic commons lemma
`Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract`
(`Submission/Commons/Topology/Homotopy/`) turns it into a *homotopy
equivalence*:

    MobiusModel ≃ₕ {c : MobiusModel // c ∈ Set.range mobiusCore}

The right-hand side is the core circle of the model (chords through the
origin, i.e. diameters).  This is the model-side of decomposition step (2c/2d)
of `Submission/Pi1Mobius.lean`; transporting it to `OpenMobius` along the
planned homeomorphism `OpenMobius ≃ MobiusModel` (first half done in
`Submission/CirclePairs.lean`) gives the deformation retraction
`OpenMobiusCoreRetract` and then the homotopy equivalence
`OpenMobius ≃ₕ (range coreFactor)` used by the `π₁(OpenMobius) ≅ ℤ`
assembly.
-/

/-- The model Möbius band is homotopy equivalent to its core circle (the
diameters `[(n, 0)]`). -/
lemma mobius_model_homotopyEquiv_core :
    Nonempty (MobiusModel ≃ₕ {c : MobiusModel // c ∈ Set.range mobiusCore}) := by
  have h := Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract
    (X := MobiusModel)
    (C := {c : MobiusModel | c ∈ Set.range mobiusCore})
    (ρ := fun z : MobiusModel × I => mobiusSlide z.1 z.2)
    continuous_mobiusSlide
    (fun c : MobiusModel => mobiusSlide_zero c)
    (fun c : MobiusModel => by
      rcases mobiusSlide_one_mem_core c with ⟨n, hn⟩
      exact Set.mem_range.mpr ⟨n, hn.symm⟩)
    (by
      intro c hc t
      rcases hc with ⟨n, hn⟩
      -- c = mobiusCore n (membership of range); the core is fixed
      rw [← hn]
      exact mobiusSlide_core_fixed n t)
  exact h

end LeanEval.KnotTheory.Quadrisecant
