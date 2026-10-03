/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N14, final wiring: the group-theoretic node inputs, discharged

`Work.ORAssembly.NodeInputs` bundles the inputs owned by the group-theoretic nodes of the route
design: node N2 (`Work.OROneRel`), node N12 (`Work.ORBassSerre`) and node N13
(`Work.ORDunwoody`).  Every one of its seven fields has since been discharged by its owner:

| field | owner | theorem used here |
|---|---|---|
| `combinatorics` | N2 | `Work.OROneRel.oneRelatorCombinatorics` |
| `hnnTree` | N12 | `Work.ORBassSerre.Assembly.hnnTreeInput` |
| `coprodTree` | N12 | `Work.ORBassSerre.Assembly.zModCoprodTreeInput` |
| `quotientTree` | N12 | `Work.ORDunwoody.quotientTreeByNormalClosureOfElliptic_holds` |
| `freeOnTree` | N12 | `Work.ORDunwoody.freeOnTreeIsFree_holds` |
| `bassSerre` | N12 | `Work.ORDunwoody.bassSerreFinitelyPresentedAll_holds` |
| `dunwoody` | N13 | `Work.ORDunwoody.dunwoodyResolutionAll_holds` |

So the group half of Theorem 1.1 no longer has any node-level hypothesis:
`Work.ORFinal.nodeInputs` fills the `HN` slot of `Work.ORAssembly.theorem_1_1_of_nodes`
(and of `Work.ORAssembly.groupCoherent_of_fgInputs`) unconditionally.

The universes: `Work.ORAssembly.theorem_1_1_of_nodes` asks for `NodeInputs.{0} Unit`, and the
node theorems above are available in every universe, so we state the discharge at `.{0}` as
required and also, for reuse, at an arbitrary universe.
-/
import Submission.Work.ORAssembly.Defs
import Submission.Work.OROneRel.oneRelatorCombinatorics
import Submission.Work.ORBassSerre.Assembly.hnnTreeInput
import Submission.Work.ORBassSerre.Assembly.zModCoprodTreeInput
import Submission.Work.ORDunwoody.Interface
import Submission.Work.ORDunwoody.DischargeResolutionAll

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORFinal

open Work.ORAssembly

/-- **The group-theoretic node inputs of the assembly, discharged.**

Every field is a theorem of its owning node; see the module docstring for the table. -/
theorem nodeInputs : NodeInputs.{0} Unit :=
  { combinatorics := Work.OROneRel.oneRelatorCombinatorics
    hnnTree := Work.ORBassSerre.Assembly.hnnTreeInput
    coprodTree := Work.ORBassSerre.Assembly.zModCoprodTreeInput
    quotientTree := Work.ORDunwoody.quotientTreeByNormalClosureOfElliptic_holds Unit
    freeOnTree := Work.ORDunwoody.freeOnTreeIsFree_holds Unit
    bassSerre := Work.ORDunwoody.bassSerreFinitelyPresentedAll_holds Unit
    dunwoody := Work.ORDunwoody.dunwoodyResolutionAll_holds Unit }

/-- The same discharge at an arbitrary universe level (the assembly only needs `.{0}`, but the
statement is level-polymorphic). -/
theorem nodeInputsOf (X : Type u) : NodeInputs.{u} X :=
  { combinatorics := Work.OROneRel.oneRelatorCombinatorics
    hnnTree := Work.ORBassSerre.Assembly.hnnTreeInput
    coprodTree := Work.ORBassSerre.Assembly.zModCoprodTreeInput
    quotientTree := Work.ORDunwoody.quotientTreeByNormalClosureOfElliptic_holds X
    freeOnTree := Work.ORDunwoody.freeOnTreeIsFree_holds X
    bassSerre := Work.ORDunwoody.bassSerreFinitelyPresentedAll_holds X
    dunwoody := Work.ORDunwoody.dunwoodyResolutionAll_holds X }

end Work.ORFinal
