import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Main.pd_window_reg

/-!
# `reg_family`: the regularity family of AJ §9 (component C16)

`P_RegFamily` for the almost Mathieu operator is the multiscale regularity output of AJ §9
(Lemmas 9.4 and 9.5): for `DiophBelow α b₀` and `λ > e^{16b₀/9}`, outside the null set `Θ`
of phases, a nonzero generalized eigenfunction `u` with `u 0 ≠ 0` produces a family of
regular sites with a uniform rate `L₁ > 0`.

The analytic content -- the continued-fraction scale selection, the two-block uniformity
(AJ Lemmas 9.6-9.13), the singular-point `A`-containment (Lemma 9.2), the Lagrange/nongen
step (Lemma 9.3), and the extraction of `IsRegular`/`IsRegularBig` (via
`regular_of_uniform`) -- is developed in `Work.TMC16Core.Core`, `Work.TMC16Core.Trig`,
`Work.TMC16Core.CF` and exposed here as the single statement `Main.pd_window_reg`.  This
file is the frozen `Basic.reg_family` interface that the C16 chain
(`Main.expLocAEpos_of_regFamily → Main.p_loc → Work.TMComp.prove_Loc`) builds on.
-/

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-- `P_RegFamily` from the Diophantine-only form of C7. -/
theorem reg_family_dioph (h0 : Work.TMC16Core.P_UniqErg) (h4 : Work.TMC16Core.P_LEBasics)
    (h7 : Work.TMC16Core.P_BJ_dioph) : Work.TMC16Core.P_RegFamily := by
  intro α b₀ lam hα hb₀ hDioph hlam E hE θ hθ u hu hu0
  exact Work.TMC16Core.Main.pd_window_reg_dioph_le h4 h7 hα hb₀ hDioph hlam hE hθ hu hu0

theorem reg_family (h0 : Work.TMC16Core.P_UniqErg) (h4 : Work.TMC16Core.P_LEBasics)
    (h7 : Work.TMC16Core.P_BJ) : Work.TMC16Core.P_RegFamily :=
  reg_family_dioph h0 h4 (Work.TMC16Core.Core.p_bj_dioph_of_p_bj h7)

end Work.TMC16Core.Basic
