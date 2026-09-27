import Submission.Work.EngulfForms.Prelude

/-!
# The fullness form `SdFullForm` (E4 repair)

`Work.Engulf.SdFullForm S` (lead's `NOTES_LEAD_poincare_E4fix.md` §5) says that after at least one
barycentric subdivision, the vertices of a face of the fine complex that lie in a union `L` of
faces of the coarse complex span a face contained in `L`.

For the concrete subdivision `Work.Engulf.subdivTools shell` of
`Submission/Work/Engulf/ToolsInstance.lean` this is exactly
`Work.PL.SubdivFull.sdIter_full` (A2), whose hypotheses `L ⊆ K.space` and "every point of `L` lies
in a face of `K` inside `L`" are precisely the two components of `Work.Engulf.IsSubSp K L`.
-/

open Set Metric PL
open Work.Engulf

namespace Work.EngulfForms

/-- **A2**: the fullness form for the concrete barycentric subdivision, from
`Work.PL.SubdivFull.sdIter_full`. -/
theorem sdFullForm {N : ℕ} (shell : SubdivShellForm N) : SdFullForm (subdivTools shell) := by
  intro r K hK L hLK hr s hs t hts ht htL
  exact Work.PL.SubdivFull.sdIter_full r K hK L hLK.1 hLK.2 hr hs hts ht htL

end Work.EngulfForms
