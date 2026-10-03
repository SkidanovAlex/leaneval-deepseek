import Mathlib
import Submission.Work.Peluse.LadderP.ladderStepP_of_lemma51P
import Submission.Work.Peluse.LadderP.concatBridgeShortB_of_ladderStepP
import Submission.Work.Peluse.PaperRoute.areaA2_of_Prop36SW
import Submission.Work.Peluse.expansionPETShortA
import Submission.Work.Peluse.ladderA_of_concatFixed

/-!
# The frozen target from the two remaining inputs, in closed form

This module is the area's "single place where the remaining hole is named".

## ROUTE CHANGE (lead, 2026-10-04 — `Submission/Work/Peluse/P2P3_LEAD.md`)

`lemma51P t` (the frozen statement of `Holds/LadderP.lean`) is proved for **every** `t ≥ 1`,
exactly as frozen, by the **regime-swap + dense-concatenation** route of `P2P3_LEAD.md` §3
(subprojects `Peluse/SwapA` — the assembly, delivering `Swap.lemma51P_all' :
∀ t ≥ 1, lemma51P t` — `Peluse/SwapC` and `Peluse/SwapE`).  The lead therefore **cancelled** the
`P1` (`LadderP.lemma54P`), `P2` (`LadderP.lemma55P`, `p2Core*`) and `P3` (`LadderP.lemma51P_succ`,
`p3Middle*`) lanes: the old induction `P1 + P2 + P3 ⟹ lemma51P_all` is **off the route**
(`P2P3_LEAD.md` §2: P2's hb-lemma route cannot be repaired; §3: P3's `a'`-pigeonhole was the
refuted step).

Consequently this file no longer uses `LadderP.lemma51P_all` (which carried the three cancelled
nodes' `sorryAx`), nor imports any of the cancelled node modules.  Until `Swap.lemma51P_all'` lands,
the full `lemma51P` is carried as a **named hypothesis**
`h51 : ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.lemma51P t`; when `Peluse/Swap/SwapA` lands,
`h51 := Work.Peluse.Swap.lemma51P_all'` discharges it, and the only remaining mathematical
hypothesis of `KMTContract_AreaA2_of_openNodes` is **O2** (unaffected by the route change,
`P2P3_LEAD.md` §0).

## The route

```
AreaA2
  ⟸ PaperRoute.areaA2_of_Prop36SW                  [PROVED, axiom-clean]
  ⟸ C46.Prop36SW P
      ⟸ O2: Work.Peluse.prop36SW_of_ladderA          [OPEN]
      ⟸ C46.PeluseLadderA
          ⟸ Work.Peluse.ladderA_of_concatFixed       [PROVED, axiom-clean]
          ⟸ UControl.PeluseConcatFixed
              ⟸ LadderP.peluseConcatFixed_of_shortsB[PROVED, axiom-clean]
              ⟸ C46.ExpansionPETShortA               [PROVED: Work.Peluse.expansionPETShortA]
              ⟸ LadderP.ConcatBridgeShortB
                  ⟸ P5 ⟸ P4 ⟸ h51 : ∀ t ≥ 1, lemma51P t      [h51 = Swap.lemma51P_all']
```

`PeluseConcatFixed_of_Pchain` below performs the `PeluseConcatFixed` step from `h51`;
`KMTContract_AreaA2_of_openNodes` composes the whole route with **O2 and `h51`** as its two named
hypotheses.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

/-- **Peluse's Theorem 3.5 in its certificate-uniform form, from the full `lemma51P`.**  This is the
`PeluseConcatFixed` step of the route: the expansion half (proved) and the bridge
`LadderP.ConcatBridgeShortB` obtained from P5 ∘ P4 ∘ `h51`. -/
theorem PeluseConcatFixed_of_Pchain
    (h51 : ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.lemma51P t) :
    Work.Peluse.UControl.PeluseConcatFixed :=
  Work.Peluse.LadderP.peluseConcatFixed_of_shortsB Work.Peluse.expansionPETShortA
    (Work.Peluse.LadderP.concatBridgeShortB_of_ladderStepP
      (Work.Peluse.LadderP.ladderStepP_of_lemma51P h51))

/-- **The frozen target `Work.KMTContract.AreaA2` from O2 and the full `lemma51P`.**  The only
mathematical hypotheses left are O2 (`Work.Peluse.prop36SW_of_ladderA`, Peluse's Proposition 3.6
from her Lemma 5.7) and `h51` (`∀ t ≥ 1, lemma51P`, delivered by `Swap.lemma51P_all'`). -/
theorem KMTContract_AreaA2_of_openNodes
    (h51 : ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.lemma51P t)
    (hO2 : ∀ P : Polynomial ℤ, 2 ≤ P.natDegree →
      Work.Peluse.C46.PeluseLadderA → Work.Peluse.C46.Prop36SW P) :
    Work.KMTContract.AreaA2 :=
  Work.Peluse.PaperRoute.areaA2_of_Prop36SW fun P hd =>
    hO2 P hd (Work.Peluse.ladderA_of_concatFixed (PeluseConcatFixed_of_Pchain h51))

/-- The same composition, kept under its former name (it *is* the "clean" form: no `sorry`-carrying
module is imported by this file, and both hypotheses are explicit). -/
theorem KMTContract_AreaA2_of_openNodes_clean
    (h51 : ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.lemma51P t)
    (hO2 : ∀ P : Polynomial ℤ, 2 ≤ P.natDegree →
      Work.Peluse.C46.PeluseLadderA → Work.Peluse.C46.Prop36SW P) :
    Work.KMTContract.AreaA2 :=
  KMTContract_AreaA2_of_openNodes h51 hO2

end

end Work.Peluse
