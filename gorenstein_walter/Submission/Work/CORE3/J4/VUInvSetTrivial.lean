import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.VUInvSetTrivial

namespace Work.CORE3.J4

open Work.GW2

/-- **Bender 1981 §3, p. 223, (5)** (area `J4` restatement): in Case (1) of Theorem 2.10, with
`V = O₂(Ĥ)` a four-group and `U = O(Ĥ)`, every involution `y ∉ Ĥ` inverts no non-trivial element
of `VU = O₂(Ĥ) ⊔ O(Ĥ)`, i.e. `I_{VU}(y) = {1}`.

This is the leaf `Work.CORE3.VUInvSetTrivial` (the unbundled form of Bender's statement (5)),
re-bracketed in the form requested by the `J4` area: `G` implicit, and the toolkit hypothesis
recorded once as `I : Case1Inputs` (whose `I.T.ft` supplies the Feit–Thompson input). -/
theorem VUInvSetTrivial {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) y = {1} :=
  _root_.Work.CORE3.VUInvSetTrivial G I hBc B h1 D

end Work.CORE3.J4
