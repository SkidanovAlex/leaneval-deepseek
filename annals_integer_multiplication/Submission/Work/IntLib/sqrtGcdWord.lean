import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.SqrtGcd.sqrtSetupJunk
import Submission.Work.IntLib.SqrtGcd.sqrtFinishEval
import Submission.Work.IntLib.SqrtGcd.gcdWord
import Submission.Work.IntLib.SqrtGcd.sqrtWord

namespace Work.IntLib

theorem sqrtGcdWord : (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.UnOp main p (fun a => 0 ≤ a) (fun a => (Nat.sqrt a.toNat : ℤ)) (fun a => K * HvdH.isz a ^ 2)) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ _ => True) (fun a b => (Int.gcd a b : ℤ)) (fun a b => K * (HvdH.isz a + HvdH.isz b) ^ 2)) := ⟨Work.IntLib.SG.sqrtWord, Work.IntLib.SG.gcdWord⟩

end Work.IntLib
