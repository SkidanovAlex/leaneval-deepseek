/-
# Existence of the core chart `Φ_v` of the `v`-th cusp

The core chart is the `OpenPartialHomeomorph (E2 × E2) E4` whose forward map is the Cartesian core
chart `ThetaCore v` (`Work.Cusp.Basic`),

  `ThetaCore v p y = (r cos θ, r sin θ, w₁, w₂)`   with `r = radial v p y`, `θ = thetaAng v p y`,

whose source is the set `coreSource v = {z | ThetaCore v z.1 z.2 ∈ coreBox}` of the cover
`(p,y) ∈ E2 × E2` that the chart sends into the open core box
`coreBox = {q | √(q 0² + q 1²) < 1/2}` (`Work.Cusp.Charts`), and whose target is exactly `coreBox`.

The explicit inverse of `ThetaCore v` is `cuspInvCore v` (`Work.Cusp.Basic`).  The four round-trip
identities are `cuspInvCore_ThetaCore` (left inverse) and `ThetaCore_cuspInvCore` (right inverse on
`coreBox`), continuity of the forward map is `ThetaCore_continuous`, and continuity of the inverse
on the target is `cuspInvCore_continuousOn`.  The source is open because it is the preimage of the
open box `coreBox` under the continuous map `ThetaCore v`.

The lemmas are in the sibling modules of this file; only the two that are needed here are imported.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.ThetaCore_continuous
import Submission.Work.Cusp.ThetaCore_injOn
import Submission.Work.Cusp.ThetaCore_cuspInvCore
import Submission.Work.Cusp.cuspInvCore_ThetaCore
import Submission.Work.Cusp.cuspInvCore_mem_coreStratum
import Submission.Work.Cusp.isOpen_coreBox
import Submission.Work.Cusp.cuspInvCore_continuousOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The source of the core chart is open.**  `coreSource v` is the preimage of the open box
`coreBox` under the continuous map `z ↦ ThetaCore v z.1 z.2` (`ThetaCore_continuous`), hence open. -/
theorem isOpen_coreSource (v : Fin 5) : IsOpen (coreSource v) :=
  isOpen_coreBox.preimage (ThetaCore_continuous v)

/-- **Existence of the core chart.**  The Cartesian core chart `ThetaCore v`, with source
`coreSource v = {z | ThetaCore v z.1 z.2 ∈ coreBox}` and target `coreBox`, is an
`OpenPartialHomeomorph (E2 × E2) E4`; its inverse is the explicit `cuspInvCore v`.

This packages the mathematical content of the module: `ThetaCore v` is continuous on its source
(`ThetaCore_continuous`), injective (`ThetaCore_injOn`), `cuspInvCore v` inverts it
(`cuspInvCore_ThetaCore`, `ThetaCore_cuspInvCore`) and is continuous on `coreBox`
(`cuspInvCore_continuousOn`), and both source and target are open (`isOpen_coreSource`,
`isOpen_coreBox`). -/
theorem exists_coreChart (v : Fin 5) :
    ∃ Φ : OpenPartialHomeomorph (E2 × E2) E4,
      Φ.source = coreSource v ∧ Φ.target = coreBox ∧
        ∀ z, Φ z = ThetaCore v z.1 z.2 := by
  refine ⟨{ toFun := fun z => ThetaCore v z.1 z.2
            invFun := cuspInvCore v
            source := coreSource v
            target := coreBox
            map_source' := fun z hz => hz
            map_target' := fun q hq => ?_
            left_inv' := fun z hz => ?_
            right_inv' := fun q hq => ?_
            open_source := isOpen_coreSource v
            open_target := isOpen_coreBox
            continuousOn_toFun := (ThetaCore_continuous v).continuousOn
            continuousOn_invFun := cuspInvCore_continuousOn v }, rfl, rfl, fun z => rfl⟩
  · -- `cuspInvCore v` lands in the source, i.e. `ThetaCore v (cuspInvCore v q) = q ∈ coreBox`
    rw [coreSource, Set.mem_ofPred_eq, ThetaCore_cuspInvCore v q hq]
    exact hq
  · -- `cuspInvCore v` is a left inverse of `ThetaCore v`
    exact cuspInvCore_ThetaCore v z.1 z.2
  · -- `cuspInvCore v` is a right inverse of `ThetaCore v` on `coreBox`
    exact ThetaCore_cuspInvCore v q hq

end Work.Cusp
