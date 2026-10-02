/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.Bridge` — the `Work.Final` vocabulary

This module converts the deliverables of `Submission/Work/PARIMPL/` into the vocabulary of the
final wiring `Submission/Work/Final/`:

* `Work.PARIMPL.ImplSide` → `Work.Final.ImplosionSide` (the structures have the same three
  fields by construction: `isOpen_Nm`, `c_mem_closure`, `period_five_gone`);
* `Work.PARIMPL.ParImplInputs.noPath` in the exact shape of the `Work.Final.FinalInputs` field
  `noPath` (the *path* form of `hLB`, replacing the old set form `noApproach`).

## Warning (import direction)

This module imports `Submission.Work.Final.Defs`.  Import it only from files that
`Submission.Work.Final.Defs` does not import, otherwise the build acquires a cycle.  The
`Work.PARIMPL` chapter itself is Final-free: use `Submission.Work.PARIMPL.All` for the
unconverted interface.
-/
import Submission.Work.Final.Defs
import Submission.Work.PARIMPL.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The implosion side data of this area **is** the `Work.Final.ImplosionSide` field of the final
wiring. -/
theorem ImplSide.toFinal {c z₁ : ℂ} {Nm : Set ℂ} (h : ImplSide c z₁ Nm) :
    Work.Final.ImplosionSide c z₁ Nm :=
  ⟨h.isOpen_Nm, h.c_mem_closure, h.period_five_gone⟩

namespace ParImplInputs

variable (H : ParImplInputs)

/-- The `impl` field of the final wiring, in the `Work.Final` vocabulary. -/
theorem impl_toFinal : Work.Final.ImplosionSide H.c₀ H.d.z₁ H.Nm := H.impl.toFinal

/-- The `noPath` field, in the exact shape of the `Work.Final.FinalInputs` field
`noPath : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mb) → c₀ ∉ closure (range γ ∩ Nm)`. -/
theorem noPath_toFinal : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) →
    H.c₀ ∉ closure (Set.range γ ∩ H.Nm) := H.noPath

end ParImplInputs

end Work.PARIMPL
