/-
# The double dual as a module, and the identity `K`-linear maps to `C`

`Work.ORHomAlg.DualMod` is a type synonym, so `DualMod (DualMod C)` and `C` are *definitionally*
equal types carrying different `K[G]`-module structures (the double dual on the one side, the
given structure on the other).  Both `TensorProduct K S (DualMod (DualMod C))` and
`TensorProduct K S C` are therefore defined, with different diagonal actions, and the task is to
compare them.

The difficulty is that Lean's tactic layer works at a transparency at which the plain `def DualMod`
does not unfold, so the two spellings cannot be unified by `rw`/`change`; moreover, if a term has
type `DualMod (DualMod C)` then type class resolution selects the dual-dual structure, while a term
of type `C` selects the given structure, and an equation between the two actions always has one
side of each kind.

The way out used here: introduce the identity maps as *named* `K`-linear maps with an explicit
codomain.  The codomain of `dualDualToCLin` is `C`, hence for `x : DualMod (DualMod C)` the term
`dualDualToCLin x` has type `C` and the instance resolved for `•` on it is the *given* structure
on `C`; likewise `dualDualToXLin y : DualMod (DualMod C)` carries the dual-dual structure.  This
makes the two module structures *separately addressable*, and lets the comparison lemmas of
`Submission/Work/ORHomAlg/Dual.lean` (`DualMod.instModuleOfRight_smul`,
`DualMod.instModuleOppositeOfLeft_smul`) be applied by `exact`/`refine` (which check definitional
equality at the default transparency) rather than by `rw`.

With these two maps the comparison can be carried out in *term mode* (`Eq.trans`, `exact`): the
elaborator checks definitional equality of implicit value arguments at the default transparency, at
which the plain `def DualMod` does unfold, so the two spellings of the type may be mixed freely.
(Making `DualMod` reducible or `[implicit_reducible]` would be an alternative, but changing the
reducibility status of `DualMod` to `reducible`/`instance_reducible` also changes type class
resolution -- the double dual then resolves to the given structure on `C`, trivialising the
statement -- and `[implicit_reducible]` does not help the rewriting tactics here, which work at
`.instances` transparency, below `.implicit`.)  No attribute is used, so the instances in the
statement of `Work.ORBridgeTor.diagDualDualEquiv` are the intended
`instDiagModule S (DualMod (DualMod C))` and `instDiagModule S C`.
-/
import Mathlib
import Submission.Work.ORHomAlg.Dual
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs

open TensorProduct MulOpposite

universe u

namespace Work.ORBridgeTor

/-- The identity, as a `K`-linear map `DualMod (DualMod C) → C`.  Its codomain is the *given*
copy of `C`, so that applications `dualDualToCLin x` carry the given `K[G]`-module structure. -/
noncomputable def dualDualToCLin (K : Type u) [Field K] (C : Type u) [AddCommGroup C]
    [Module K C] : Work.ORHomAlg.DualMod (Work.ORHomAlg.DualMod C) →ₗ[K] C where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity, as a `K`-linear map `C → DualMod (DualMod C)`.  Its codomain is the *double
dual*, so that applications `dualDualToXLin y` carry the dual-dual `K[G]`-module structure. -/
noncomputable def dualDualToXLin (K : Type u) [Field K] (C : Type u) [AddCommGroup C]
    [Module K C] : C →ₗ[K] Work.ORHomAlg.DualMod (Work.ORHomAlg.DualMod C) where
  toFun y := y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem dualDualToCLin_apply (K : Type u) [Field K] (C : Type u) [AddCommGroup C] [Module K C]
    (x : Work.ORHomAlg.DualMod (Work.ORHomAlg.DualMod C)) :
    dualDualToCLin K C x = x := rfl

@[simp]
theorem dualDualToXLin_apply (K : Type u) [Field K] (C : Type u) [AddCommGroup C] [Module K C]
    (y : C) : dualDualToXLin K C y = y := rfl

end Work.ORBridgeTor
