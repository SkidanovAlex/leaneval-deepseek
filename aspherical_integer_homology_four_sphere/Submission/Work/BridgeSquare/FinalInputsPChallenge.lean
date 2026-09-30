/-
# `BridgeSquare/FinalInputsPChallenge.lean` — the challenge theorem in the `P` wiring

The two theorems of the redesign (`Submission/Work/NOTES_LEAD_aspherical_bridge.md` §1.2) that need
the consumer:

* `Work.Final.isIntegerHomologySphere_Mhat4P` — `H_*(M̂)` from `Work.BridgeSquare.intHomology_of_props`
  (the `SurjCert`/`KernelCert` route: the bridge square is no longer an input) and the sphere
  computation `Work.Homology.intHomology_sphere_four`;
* `Work.Final.aspherical_integer_homology_four_sphere_P` — the challenge statement from a single
  `instance : Work.Final.FinalInputsP`.

The remaining mathematical input is therefore exactly
`Work.Final.FinalInputsP.hsurj` and `.hker` for `L = Work.HomologyIso.mhatLES`, i.e. (by
`Work.BridgeSquare.mvFhat_conj_cuspPair`) properties of the cusp pair `F_k = (H_k τ, H_k π)`:

| degree | needed | where |
|---|---|---|
| `0` | injective | `Work.BridgeSquare.cuspPair_injective_zero` (section + ranks) |
| `1, 2` | surjective | **(a)** + **(c)** of `NOTES_LEAD_aspherical_bridge.md` §2.3 |
| `3` | surjective | **(c)** |
| `≥ 4` | trivial | `Work.BridgeSquare.squareAt_of_ge_four`, ranks `0` |
-/
import Submission.Work.BridgeSquare.FinalInputsP
import Submission.Work.BridgeSquare.intHomology_of_props

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.defProp false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

open LeanEval.Topology
open CategoryTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Work.Final

open Work.Space

noncomputable section

/-- **`M̂` is an integer homology 4-sphere**, from the `P` properties of the Mayer–Vietoris map:
`Work.BridgeSquare.intHomology_of_props` computes `H_*(M̂)` from `L`, `hsurj`, `hker` (no bridge
square, no `wConcrete`), and `Work.Homology.intHomology_sphere_four` closes the target. -/
theorem isIntegerHomologySphere_Mhat4P [D : FinalInputsP] :
    (Mhat4P (D := D)).IsIntegerHomologySphere := by
  intro k
  obtain ⟨eX⟩ :=
    Work.BridgeSquare.intHomology_of_props D.L D.eM D.eN D.hsurj D.hker D.hX
      (FinalInputsP.h0_of_hX (D := D)) k
  obtain ⟨eS⟩ := Work.Homology.intHomology_sphere_four k
  exact ⟨eX ≪≫ eS.symm⟩

/-- **THE CHALLENGE THEOREM in the `P` wiring**: a single `instance : Work.Final.FinalInputsP`
makes the challenge statement unconditional.  The fields of `FinalInputsP` are the assembled space,
the smoothness and the curvature bound (all discharged by the delivered areas), the two
`Nonempty`-valued identifications of the Mayer–Vietoris slots (any isos will do), and the two
properties `hsurj`/`hker` of the actual map `L.d (k,0)`. -/
theorem aspherical_integer_homology_four_sphere_P [D : FinalInputsP] :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  ⟨Mhat4P (D := D), isAspherical_Mhat4P (D := D), isIntegerHomologySphere_Mhat4P (D := D)⟩

end

end Work.Final
