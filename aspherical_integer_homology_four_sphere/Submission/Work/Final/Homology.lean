/-
# `Final/`: `M̂` is an integer homology 4-sphere

This file wires the Mayer–Vietoris computation of `Work.HomologyMV` into the challenge's
`IsIntegerHomologySphere`, in the shape of the blueprint:

```
theorem hs : Mhat4.IsIntegerHomologySphere :=
  fun k ↦ ⟨(HMV.Mhat_homology k).some ≪≫ (S2.sphere4 k).some.symm⟩
```

* `Work.HomologyMV.intHomology_of_concrete` (`HomologyMV/Main.lean`) takes
  the Mayer–Vietoris long exact sequence `L` of the cover `M̂ = A ∪ B`, the identifications
  `eM`, `eN` of its first two slots with the free models `ModelM`, `ModelN`, the commuting square
  `hsq` with the concrete matrix `wConcrete`, the identification `hX` of the `X`-slot with the
  singular homology of `M̂`, and `h0 : H_0(M̂) ≅ ℤ`; it returns
  `intHomology k M̂ ≅ (if k = 0 ∨ k = 4 then ℤ else 0)`.
* `Work.Homology.intHomology_sphere_four` is the same computation for the standard 4-sphere.
* Their composite is the required `intHomology k M̂ ≅ intHomology k S⁴`.
-/
import Submission.Work.Final.Mhat

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

/-- **`M̂` is an integer homology 4-sphere.**  In every degree, `H_k(M̂; ℤ)` is isomorphic to
`H_k(S⁴; ℤ)`: `ℤ` for `k = 0, 4` and `0` otherwise.

The computation is `Work.HomologyMV.intHomology_of_concrete` on the Mayer–Vietoris sequence of
the cover `M̂ = A ∪ B` (`Work.Space.Assembly.Aset_sup_Bset`), composed with the sphere
computation `Work.Homology.intHomology_sphere_four`. -/
theorem isIntegerHomologySphere_Mhat4 [D : FinalInputs] :
    (Mhat4 (D := D)).IsIntegerHomologySphere := by
  intro k
  obtain ⟨eX⟩ :=
    Work.HomologyMV.intHomology_of_concrete D.L D.eM D.eN D.hsq D.hX
      (FinalInputs.h0_of_hX (D := D)) k
  obtain ⟨eS⟩ := Work.Homology.intHomology_sphere_four k
  exact ⟨eX ≪≫ eS.symm⟩

end

end Work.Final
