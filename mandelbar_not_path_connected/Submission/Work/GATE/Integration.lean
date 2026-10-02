/-
# Integration with `Work.Final.FinalInputs`

`Work.GATE.TwoSided c₀ Nm` is *definitionally* the `twoSided` field of
`Work.Final.FinalInputs` (`Submission/Work/Final/Main.lean`), so the lead can fill that field by

```lean
twoSided := Work.GATE.twoSided hOpen hfront TD G
```

and the two examples below are the machine-checked statement of that fact (they are `rfl`-typed:
the `exact h` goes through by definitional unfolding, with no rewriting).
-/
import Submission.Work.GATE.TwoSided

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE

open LeanEval.ComplexAnalysis (Mandelbar)

/-- **`Work.GATE.TwoSided` is the `twoSided` field, verbatim.** -/
example {c₀ : ℂ} {Nm : Set ℂ} (h : TwoSided c₀ Nm) :
    ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
      ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
      Work.ParamRays.extAngle e₁ ∈ Set.Ioo (Work.Final.alpha1 - Work.Final.windowEps)
        (Work.Final.alpha1 + Work.Final.windowEps) ∧
      Work.ParamRays.extAngle e₂ ∈ Set.Ioo (Work.Final.alpha2 - Work.Final.windowEps)
        (Work.Final.alpha2 + Work.Final.windowEps) :=
  h

/-- **The theorem at the field's type.** -/
example {c₀ : ℂ} {Nm : Set ℂ} (hOpen : IsOpen Nm) (hfront : c₀ ∈ frontier Nm)
    (TD : TransitData c₀ Nm) (G : GateAngle c₀ Nm TD) :
    ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
      ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
      Work.ParamRays.extAngle e₁ ∈ Set.Ioo (Work.Final.alpha1 - Work.Final.windowEps)
        (Work.Final.alpha1 + Work.Final.windowEps) ∧
      Work.ParamRays.extAngle e₂ ∈ Set.Ioo (Work.Final.alpha2 - Work.Final.windowEps)
        (Work.Final.alpha2 + Work.Final.windowEps) :=
  twoSided hOpen hfront TD G

/-- **The frontier hypothesis of `twoSided`, from the `Final` vocabulary.**  In the endgame the
point `c₀` is on the frontier of the implosion side: this is
`Work.Final.RootArc.mem_frontier_Nm`, recorded here in the form in which `Work.GATE.twoSided`
consumes it. -/
theorem mem_frontier_of_implSide {c : ℂ} {Nm : Set ℂ} (A : Work.Final.RootArc c)
    (h : Work.Final.ImplosionSide c A.d.z₁ Nm) : c ∈ frontier Nm :=
  A.mem_frontier_Nm h

end Work.GATE
