import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1aA7V18

namespace Work.CORE3

open Work.GW2

/-- Bender 1981 §3, p. 222, the `M`-step of the subcase `Ĥ = H`: for a coatom
`M ⊇ N_G(P₂)`, `S ≤ M`, `⟨t,t₂⟩ ≤ E(M)`, `E(M)/Z(E(M)) ≅ A₇`, `|S| = 8` and
`|O_p(U) ⊓ M| = 3` (the design leaf `Work.GW2.Case1aA7Prop`).

Proved in `Submission/Work/CORE3/Case1aA7V18.lean`, which assembles the `A7V18/*` sub-tree
(`P0ne`, `NP2NotH`, `V2LayerMne`, `A7QuotientD`, `SylowEight`, `P0Card`). -/
theorem Case1aA7 (I : Case1Inputs) (hFr : Case1aFrattiniProp) (hAb : Case1aAbelianProp) :
    Case1aA7Prop :=
  Case1aA7V18 I hFr hAb

end Work.CORE3
