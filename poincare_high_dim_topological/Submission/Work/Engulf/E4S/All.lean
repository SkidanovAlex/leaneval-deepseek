import Submission.Work.Engulf.E4S.Basic
import Submission.Work.Engulf.E4S.PushShellG
import Submission.Work.Engulf.E4S.PushStep2
import Submission.Work.Engulf.E4S.Step
import Submission.Work.Engulf.E4S.StepG
import Submission.Work.Engulf.E4S.piecesEngulfG
import Submission.Work.Engulf.E4S.face_subset_of_subset_iUnion

/-!
# `Work.Engulf.E4S.All` — the moving-map step of Newman's Lemma 7 Case 1

Area E4S (`Submission/Work/NOTES_LEAD_poincare_E4c.md` §A.4–A.5) of the Poincare project: the
`E4d` push with a moving map, the `E4e` step preserving `AltInnerG`, and the two support lemmas
(transfer and dimension bound).

## Interface

| entry point | module | what it is |
|---|---|---|
| `Work.Engulf.E4S.pushShellG` | `E4S.PushShellG` | `E4d` with an arbitrary map `g` (the `∪` restored, `hG`/`hcore` dropped) |
| `Work.Engulf.E4S.pushStep2_of_pushShellG` | `E4S.PushStep2` | `Work.Engulf.E4Aux.pushStep2` as the case `g := ND.g₁` |
| `Work.Engulf.E4S.stepG_of_pieces` | `E4S.Step` | one loop step, with the piece loop `E4c` as an explicit hypothesis |
| `Work.Engulf.E4S.eq_g₁_of_mem_closedCube` | `E4S.Basic` | the transfer lemma (margin `μ` of `exists_core_margin`) |
| `Work.Engulf.E4S.eq_g₁_of_near` | `E4S.Basic` | the same in `near`-form |
| `Work.Engulf.E4S.card_le_of_simp_subset_K_union_Q` | `E4S.Basic` | `hGdim` for `G = K ∪ Q` |
| `Work.Engulf.E4S.altInnerG_zero` | `E4S.Basic` | the base case `i = 0`, `g = g₁`, `h = refl` |

`Work.Engulf.E4S.stepG` (the unconditional statement, §A.5) lives in `E4S.StepG`, which imports the
piece loop `E4c` (`Work.Engulf.E4Aux.piecesEngulfG`, area E4P).  It is kept in a separate module so
that everything else in this area is independent of the piece loop's proof.
-/

