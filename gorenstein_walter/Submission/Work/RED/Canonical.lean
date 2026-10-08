import Submission.Work.RED.NonSimpleStep
import Submission.Work.ASM.Defs

/-!
# RED in the canonical `Work.GW2` vocabulary

`Submission.Work.ASM.Defs` is a shared home of the `Work.GW2` vocabulary (a verbatim copy
of `_design_gw/Contracts2.lean`).  `Work.RED.GW2.Defs` is a second verbatim copy of the same
contracts, so the two vocabularies are definitionally equal and the RED deliverable can be
restated without any transport.
-/

namespace Work.GW2

/-- The non-simple step in the canonical vocabulary, from the full local toolkit. -/
theorem nonSimpleStep_of_RED (T : LocalToolkit) : NonSimpleStepProp :=
  Work.RED.GW2.nonSimpleStep T.ft T.fus T.split T.autL2 T.autA7

end Work.GW2

namespace Work.GW2

/-- The two vocabularies are definitionally equal: this is the statement RED proves. -/
theorem nonSimpleStepProp_iff : Work.RED.GW2.NonSimpleStepProp ↔ NonSimpleStepProp := Iff.rfl

/-- The non-simple step in the canonical vocabulary, from the individual toolkit Props. -/
theorem nonSimpleStep_of_props (hft : FeitThompsonProp) (hfus : InvolutionFusionProp)
    (hsplit : CentralizerSplitProp) (hautL2 : AutL2Prop) (hautA7 : AutA7Prop) :
    NonSimpleStepProp :=
  Work.RED.GW2.nonSimpleStep hft hfus hsplit hautL2 hautA7

end Work.GW2
