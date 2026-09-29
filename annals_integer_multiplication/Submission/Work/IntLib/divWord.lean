import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Raw
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.divCore
import Submission.Work.IntLib.divPush
import Submission.Work.IntLib.divAsm

namespace Work.IntLib

open HvdH

/-- The four `BinOp`s of `IntLib` for truncated and floor division/modulus.  Each program is
`Div.coreRun` (markers + parse + long division) followed by the corresponding fix-up. -/
theorem divWord : (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ b => b ≠ 0) Int.tdiv (fun a b => K * HvdH.isz a * HvdH.isz b)) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ b => b ≠ 0) Int.tmod (fun a b => K * HvdH.isz a * HvdH.isz b)) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ b => 0 < b) Int.fdiv (fun a b => K * HvdH.isz a * HvdH.isz b)) ∧ (∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ b => 0 < b) Int.fmod (fun a b => K * HvdH.isz a * HvdH.isz b)) := by
  refine ⟨⟨Div.divProgTdiv, 1000, fun main => ?_⟩, ⟨Div.divProgTmod, 1000, fun main => ?_⟩,
    ⟨Div.divProgFdiv, 1000, fun main => ?_⟩, ⟨Div.divProgFmod, 1000, fun main => ?_⟩⟩
  · exact Div.div_tdiv_word main
  · exact Div.div_tmod_word main
  · exact Div.div_fdiv_word main
  · exact Div.div_fmod_word main

end Work.IntLib
