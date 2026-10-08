/-
Alias file: the design name `Work.BG.s02_noFailThm` for the proved N-1 leaf
`Work.BG.noFail` (`BG/noFail.lean`).

This file used to contain a second, independent copy of the whole proof of `NoFailProp`
(with its own helper `Work.BG.nfRep`), which made it impossible to import together with
`BG/noFail.lean` (duplicate declaration).  It now re-exports the single proof; the helpers it
used to declare (`nfRep`, `nf_sconj_apply_t`, …) are in `BG/noFail.lean`.
-/
import Submission.Work.BG.noFail

namespace Work.BG

theorem s02_noFailThm {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.NoFailProp C :=
  noFail C

end Work.BG
