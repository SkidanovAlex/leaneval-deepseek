/-
# C16: Anderson localisation for large coupling (AJ §9) -- assembly

The component `P_Loc` is assembled from the AJ §9 regularity output (`Basic.reg_family`),
the patching step (`Main.expLocAEpos_of_regFamily`) and the two-sided upgrade
(`Main.expLocAE_of_pos`).
-/
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.reg_family
import Submission.Work.TMC16Core.Main.expLocAEpos_of_regFamily
import Submission.Work.TMC16Core.Main.expLocAE_of_pos

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC16Core.Main

/-- **C16** (AJ Thm 5.2 = Thm 9.1, §9): Anderson localisation for `λ > e^{16β/9}`.
Consumes the components `C0` (`P_UniqErg`), `C1` (`P_OpBasics`), `C4` (`P_LEBasics`) and
`C7` **in its Diophantine-only form** (`P_BJ_dioph`), which is all AJ §9 uses (`L = log λ`
on the spectrum, with `DiophBelow α b₀`, `b₀ > 0`). -/
theorem p_loc_dioph (h0 : Work.TMC16Core.P_UniqErg) (h1 : Work.TMC16Core.P_OpBasics)
    (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ_dioph) :
    Work.TMC16Core.P_Loc := by
  intro α b₀ lam hα hb₀ hD hlam
  exact Work.TMC16Core.Main.expLocAE_of_pos
    (Work.TMC16Core.Main.expLocAEpos_of_regFamily h0 h1 h4 h7
      (Work.TMC16Core.Basic.reg_family_dioph h0 h4 h7) α b₀ lam hα hb₀ hD hlam)

/-- The historical form, consuming the full `C7` (`P_BJ`). -/
theorem p_loc (h0 : Work.TMC16Core.P_UniqErg) (h1 : Work.TMC16Core.P_OpBasics)
    (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ) :
    Work.TMC16Core.P_Loc :=
  p_loc_dioph h0 h1 h4 (Work.TMC16Core.Core.p_bj_dioph_of_p_bj h7)

end Work.TMC16Core.Main
