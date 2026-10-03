import Mathlib
import Submission.Work.Peluse.PaperRoute.crux_of_nodes_paper
import Submission.Work.Peluse.PaperRoute.ucontrolPaper_of_piecePet
import Submission.Work.Peluse.ulowering_of
import Submission.Work.Peluse.u2inverse
import Submission.Work.Peluse.majorarc
import Submission.Work.Peluse.Compatible

/-!
# Q4 — the assembly of the frozen target `AreaA2` from the chapter `PiecePet`

`CONCAT_AUDIT_LEAD.md` §3 gives the corrected chain

```
AreaA2 ← AreaA2_of_crux (proved) ← crux ← [Q2 ucontrolPaper_of_piecePet, Q3 crux_of_nodes_paper]
                                         ← PiecePet P
PiecePet P ← piecePet_of_prop36SW (O1, §5 lane) + prop34Holds (proved)
```

Everything except the chapter `PiecePet` is here: `AreaA2_of_crux`, `ulowering_of`, `u2inverse`,
`majorarc` are proved, and Q2/Q3 are the wiring in this directory.  The theorem below therefore
*is* the assembly, stated with the chapter as a hypothesis so that it does not depend on the §5
lane's files (which live under `Work.Peluse.Holds` / the O1–O6 nodes of the audit;
`substitute one line` when `piecePet_of_prop36SW` and the corrected `Prop36SW` land).

The hypothesis is the level-fixed form `Work.Peluse.UControl.PiecePetTwo` (see
`PaperRoute/PiecePetTwo.lean`: `PiecePet`'s body with the level recorded as `2 ≤ s₀`, which is what
every consumer needs and what every level-`s ≥ 2` producer of the chapter gives verbatim); the form
`PiecePet` recorded in the tree's frozen statement layer is *weaker* than its own producers, since it
records only `1 ≤ s₀`.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.PaperRoute

noncomputable section

/-- **Q4**: the frozen target `Work.KMTContract.AreaA2` from the chapter `PiecePet` (in its
level-`≥ 2` form) — the full wiring, with the §5 lane's chapter as the only hypothesis. -/
theorem area_a2_of_piecePet
    (h : ∀ P : Polynomial ℤ, 2 ≤ P.natDegree → Work.Peluse.UControl.PiecePetTwo P) :
    Work.KMTContract.AreaA2 :=
  Work.Peluse.areaA2_iff.mpr (Work.Peluse.AreaA2_of_crux fun P hd =>
    crux_of_nodes_paper hd
      (ucontrolPaper_of_piecePet P hd (h P hd))
      (Work.Peluse.ulowering_of hd Work.Peluse.u2inverse (Work.Peluse.majorarc hd)))

end

end Work.Peluse.PaperRoute
