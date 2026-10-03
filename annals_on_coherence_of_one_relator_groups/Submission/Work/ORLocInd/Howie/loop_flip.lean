import Mathlib
import Submission.Work.ORLocInd.Howie.LoopAux

namespace Work.ORLocInd.Howie

open Quiver

universe u

/-- Flipping the sign of a term inverts its loop: `loop (flip t) = (loop t)⁻¹`.

Both sides are reduced closed paths at `v`; unwinding the definitions they are

`δ · (α^{∓1}) · δ⁻¹`  and  `(δ · α^{±1} · δ⁻¹)⁻¹`,

so the statement is the path identity `(δ · β · δ⁻¹)⁻¹ = δ · β⁻¹ · δ⁻¹`, which follows from
`pmul_reverse_comp` (reversal reverses the groupoid product) and associativity of `pmul`. -/
theorem loop_flip {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} (t : Work.ORLocInd.Howie.RelatorTerm P v) :
    Work.ORLocInd.Howie.RelatorTerm.loop (Work.ORLocInd.Howie.RelatorTerm.flip t) =
      (Work.ORLocInd.Howie.RelatorTerm.loop t)⁻¹ := by
  apply Subtype.ext
  show pmul t.δ (pmul (RelatorTerm.signedPath (RelatorTerm.flip t)) t.δ.reverse) =
    (pmul t.δ (pmul t.signedPath t.δ.reverse)).reverse
  rw [RelatorTerm.signedPath_flip]
  rw [pmul_reverse_comp, pmul_reverse_comp, Quiver.Path.reverse_reverse]
  rw [pmul_assoc]
  rfl

end Work.ORLocInd.Howie

