/-
# `Final/`: the challenge theorem, modulo `FinalInputs`

```
theorem aspherical_integer_homology_four_sphere : ∃ M : Closed4Manifold, M.IsAspherical ∧ …
```

with `M := Mhat4`, the asphericity from Cartan–Hadamard (`isAspherical_Mhat4`) and the homology
computation from Mayer–Vietoris (`isIntegerHomologySphere_Mhat4`).

Once the areas `Space`, `LeviCivita`, `Curvature`, `DeltaHomology` and `Certificates` have
delivered, inhabiting `Work.Final.FinalInputs` (a single `instance`) turns this into the
unconditional theorem; see `NOTES_FINAL.md` for the exact list of fields and their owners.
-/
import Submission.Work.Final.Homology

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

open LeanEval.Topology
open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Work.Final

open Work.Space

noncomputable section

/-- **Existence of an aspherical integer homology 4-sphere**, modulo the final inputs.

This is the statement of `Challenge.lean`, proved from a single `instance : FinalInputs`; the
manifold is `Mhat4 = M̂`, its asphericity is `isAspherical_Mhat4` (Cartan–Hadamard) and its
homology is `isIntegerHomologySphere_Mhat4` (Mayer–Vietoris). -/
theorem aspherical_integer_homology_four_sphere [D : FinalInputs] :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  ⟨Mhat4 (D := D), isAspherical_Mhat4 (D := D), isIntegerHomologySphere_Mhat4 (D := D)⟩

end

end Work.Final
