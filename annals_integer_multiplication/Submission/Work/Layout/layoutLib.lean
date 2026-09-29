import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.lengthWord
import Submission.Work.Layout.reverseWord
import Submission.Work.Layout.appendWord
import Submission.Work.Layout.takeDropWord
import Submission.Work.Layout.replicateWord
import Submission.Work.Layout.flattenWord
import Submission.Work.Layout.chunksOfWord
import Submission.Work.Layout.enumerateWord
import Submission.Work.Layout.sortByKeyWord
import Submission.Work.Layout.applyAlongWord

/-!
Guidance from the project lead (the requester):

AREA OWNER: Layout. You prove `HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib` (Interfaces.lean, lead-owned).
Read HANDOFF.md. Use the KernelLib/IntLib hypotheses and the raw toolkit in `Submission/Work/Kernel/` when
present. Delegate the list words in parallel; `sortByKey` and `applyAlong` are the two heavy pieces.

Assembly: `Submission/Work/Layout/Move.lean` provides the marker-based value movers (`mvVal` etc.),
`Base.lean` the `Ev`/`loopRuns` toolkit, and each field of `LayoutLib` is proved in its own file by a
member of the team (`lengthWord`, `reverseWord`, `appendWord`, `takeDropWord`, `replicateWord`,
`flattenWord`, `chunksOfWord`, `enumerateWord`, `sortByKeyWord`, `applyAlongWord`).
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-- List and array layout words (sorting, slices, applyAlong). -/
theorem layoutLib : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib := by
  intro _hK hI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lengthWord hI
  · exact reverseWord
  · exact appendWord
  · exact takeDropWord.1
  · exact takeDropWord.2
  · exact replicateWord hI
  · exact flattenWord
  · exact chunksOfWord
  · exact enumerateWord hI
  · exact sortByKeyWord hI
  · exact applyAlongWord _hK hI

end Work.Layout
