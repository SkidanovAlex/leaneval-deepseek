import Mathlib
import Submission.Work.LEAD.Core27
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4._copy_main

namespace Work.CORE4

/-- **`L2pLocalProp → CopyLocalProp`** (design pass 27, Bender §4 p. 227).  Proved in
`Submission/Work/CORE4/_copy_main.lean` (`Work.CORE4.main_assembly`) from the single-copy
`L₂(q)` input together with

* `Work.CORE4.normalizer_diag_iff` / `Work.CORE4.CopyLocalDiagFixed` (`CopyLocalDiagFixed.lean`):
  the normaliser of a diagonal `⟨a t⟩` inside `P ⊔ E`;
* `Work.CORE4.CopyLocalPPart` (`CopyLocalPPart.lean`): `p² ∤ |D|`;
* `Work.CORE4.CopyLocalCount` (`CopyLocalCount.lean`): the `≡ 1 (mod 2p)` and `≤ q` count;
* `Work.CORE4.PGroupActionCentralizer` (`PGroupActionCentralizer.lean`). -/
theorem CopyLocal27 : Work.GW2.C27.L2pLocalProp → Work.GW2.C27.CopyLocalProp :=
  main_assembly

end Work.CORE4
