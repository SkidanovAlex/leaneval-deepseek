/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : the deliverable

`Work.AUTL2.autL2Prop` is the statement contracted for the area, `Work.GW2.AutL2Prop`
(`Submission/Work/_design_gw/Contracts2.lean`), proved by composing

* `Work.AUTL2.Main.autL2` — the transfer from an abstract overgroup `Q ≥ L ≅ PSL(2,q)` with
  `C_Q(L) = 1` and cyclic-or-dihedral Sylow 2-subgroups to the concrete model on `ℙ¹(F_q)`,
  where the Sylow analysis (`Work.AUTL2.Main.a5odd`) applies.

A caller who needs the contract statement should cite

```lean
import Submission.Work.AUTL2.Main.bridge
example : Work.GW2.AutL2Prop := Work.AUTL2.autL2Prop
```
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Main.autL2

open scoped MatrixGroups

namespace Work.AUTL2

/-- **AREA AUTL2 deliverable**: `Work.GW2.AutL2Prop`.

Let `L ◁ Q` with `L ≃ PSL(2,q)` (`q = p^k`, `p` odd, `q ≥ 5`), `C_Q(L) = 1`, and let `Q` have
cyclic or dihedral Sylow 2-subgroups. Then `Q` has a normal subgroup `M ⊇ L` of odd index with
`M ≃ PSL(2,q)` or `M ≃ PGL(2,q)`. -/
theorem autL2Prop : Work.GW2.AutL2Prop := by
  intro Q hG hF L p k hFact hp hq hL he hC hdih
  obtain ⟨e⟩ := he
  exact Main.autL2 p k Q L e hp hq hL hC hdih

end Work.AUTL2
