import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.MainP.crtDefs
import Submission.Work.MainP.crtMath
import Submission.Work.MainP.crtLib
import Submission.Work.MainP.crtTail
import Submission.Work.MainP.crtWordAux
import Submission.Work.MainP.crtPrep
import Submission.Work.MainP.crtBranch0
import Submission.Work.MainP.crtBranch1
import Submission.Work.MainP.crtJoinWord2
import Submission.Work.MainP.crtStripWord
import Submission.Work.MainP.crtLabWord
import Submission.Work.MainP.crtSorted

/-! Guidance from the project lead (the requester):

AREA OWNER: CrtWord (Agarwal–Cooley reindexing; split out of Main by the lead). Prove
`KernelLib → IntLib → LayoutLib → CrtWordProp`. Math: for pairwise coprime sᵢ ≥ 1, m ↦ crtIdx ss m is a bijection
of [0, S) (CRT; Mathlib `Nat.chineseRemainder`, `Nat.Coprime` products); crtIdx = undigits of the residues
(H9 already proved the same facts for its identical `Work.Main.Pcr`: Pcr_lt, Pcr_inj, Pcr_mod — reuse by rfl).

The word is assembled in `Submission/Work/MainP/crtWordAux.lean` (prep, then `if dir = 0` → label-and-sort
with the labels `sigmaList ss`, else build the inverse permutation `crtQ ss` and label-and-sort with it),
from the library-level words `crtJoinWord2` (elementwise record join), `crtStripWord` (strip the keys),
`crtLabWord` (the label list `sigmaList ss`) and the sorting characterisation `crtSorted`.
-/

set_option autoImplicit false

namespace Work.MainP

/-- Agarwal-Cooley reindexing word and its inverse (label and sort). -/
theorem crtWord : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.CrtWordProp := by
  intro hK hI hL
  have pieces : CrtPieces :=
    { join := crtJoinWord2 hK hI hL
      strip := crtStripWord hK hI hL
      lab := crtLabWord hK hI hL
      sorted := fun hxs hlab hinj hlt => crtSorted hxs hlab hinj hlt }
  have parts : CrtParts hK hI hL :=
    { prep := fun L => crtPrep L
      b0 := fun L => crtBranch0 L
      b1 := fun L => crtBranch1 L }
  exact crtWord_aux hK hI hL pieces parts

end Work.MainP
