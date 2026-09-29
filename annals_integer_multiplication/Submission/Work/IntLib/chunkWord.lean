import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.chunksAPI
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.Shift.Base
import Submission.Work.IntLib.Shift.Defs
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Kernel.Raw
import Submission.Work.IntLib.chunkAssembly
import Submission.Work.IntLib.chunkEv

namespace Work.IntLib

theorem chunkWord : (∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (x b N : ℕ), 1 ≤ b → x < 2 ^ (b * N) → HvdH.WordR main p (fun vs => ∃ rest, vs = .int x :: .int b :: .int N :: rest) (fun vs out => ∃ rest, vs = .int x :: .int b :: .int N :: rest ∧ out = HvdH.intList (HvdH.chunks x b N) :: rest) (fun _ => K * (HvdH.isz x + N * (b + 1) + HvdH.isz b + HvdH.isz N))) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (hs : List ℕ) (b : ℕ), 1 ≤ b → (∀ h ∈ hs, h < 2 ^ (3 * b)) → HvdH.WordR main p (fun vs => ∃ rest, vs = HvdH.intList hs :: .int b :: rest) (fun vs out => ∃ rest, vs = HvdH.intList hs :: .int b :: rest ∧ out = .int (HvdH.evalChunks hs b) :: rest) (fun _ => K * ((hs.map fun h => HvdH.isz h).sum + hs.length * (b + 1) + HvdH.isz b + 1))) := by
  exact ⟨chunkWord_chunk, chunkWord_poly⟩

end Work.IntLib
