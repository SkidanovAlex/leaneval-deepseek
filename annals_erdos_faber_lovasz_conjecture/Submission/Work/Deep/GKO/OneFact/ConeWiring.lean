import Submission.Work.Deep.GKO.OneFact.gkoStatementFixed_of_oneFact
import Submission.Work.Deep.GKO.OneFact.N5.oneFactLowerReg_elementary
import Submission.Work.Deep.GKO.ConeBridge

/-!
# The cone wiring of the one-factorization route

The cone's `ErdosFaberLovaszConjecture.GKOStatement` (KKKMO Theorem 10.8, the hole `hGKO` of
`Submission.lean`) now follows from the chapter's new deep input
`Work.Deep.GKO.OneFactLowerRegStatement`:

* `Work.Deep.GKO.OneFact.gkoStatementFixed_of_oneFact` — the new N6 step, replacing the retired
  `gkoStatementFixed_of_KO` (which consumed `KOStatement`);
* `Work.Deep.GKO.gkoStatement_of_fixed` — the proved bridge
  `GKOStatementFixed → ErdosFaberLovaszConjecture.GKOStatement`.

The remaining input is supplied by
`Work.Deep.GKO.OneFact.oneFactLowerReg_of_approxHam : ApproxHamDecompStatement →
OneFactLowerRegStatement` (node N5, which rests on the matching absorber N1 and the sampling nodes
N2, N3), so the cone's one line becomes

```lean
have hGKO : ErdosFaberLovaszConjecture.GKOStatement :=
  Work.Deep.GKO.OneFact.gkoStatement_of_approxHam
    Work.Deep.GKO.OneFact.approxHamDecompStatement
```

where the last factor is S750's discharge of `ApproxHamDecompStatement`.
-/

namespace Work.Deep.GKO.OneFact

/-- **The cone's GKO hole from the one-factorization input.** -/
theorem gkoStatement_of_oneFact (hOne : Work.Deep.GKO.OneFactLowerRegStatement) :
    ErdosFaberLovaszConjecture.GKOStatement :=
  Work.Deep.GKO.gkoStatement_of_fixed
    (Work.Deep.GKO.OneFact.gkoStatementFixed_of_oneFact hOne)

/-- **The cone's GKO hole, closed by the elementary one-factorization route**: the deep input
`Work.Deep.GKO.OneFactLowerRegStatement` is proved in
`Work.Deep.GKO.OneFact.N5.oneFactLowerReg_elementary` (balanced cut + Vizing on the inside graph +
alternating-path completion + the matching absorber N1), so
`ErdosFaberLovaszConjecture.GKOStatement` needs no further input. -/
theorem gkoStatement_elementary : ErdosFaberLovaszConjecture.GKOStatement :=
  gkoStatement_of_oneFact Work.Deep.GKO.OneFact.N5.oneFactLowerReg_elementary

end Work.Deep.GKO.OneFact
