import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.Shift.Defs
import Submission.Work.IntLib.Shift.Assembly

namespace Work.IntLib

theorem shiftWord : (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ k => 0 ≤ k) (fun a k => a * 2 ^ k.toNat) (fun a k => K * (HvdH.isz a + k.toNat + HvdH.isz k))) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ k => 0 ≤ k) (fun a k => Int.tdiv a (2 ^ k.toNat)) (fun a k => K * (HvdH.isz a + HvdH.isz k))) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ k => 0 ≤ k) (fun a k => Int.fdiv a (2 ^ k.toNat)) (fun a k => K * (HvdH.isz a + HvdH.isz k))) := by
  refine ⟨⟨Shift.shlProg, 4000, fun main => Shift.shlWordProg main⟩,
    ⟨Shift.shrTProg, 4000, fun main => Shift.shrTWordProg main⟩,
    ⟨Shift.shrFProg, 4000, fun main => Shift.shrFWordProg main⟩⟩

end Work.IntLib
