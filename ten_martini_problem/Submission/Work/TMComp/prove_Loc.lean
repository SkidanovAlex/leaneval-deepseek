import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.prove_UniqErg
import Submission.Work.TMComp.prove_OpBasics
import Submission.Work.TMComp.prove_LEBasics
import Submission.Work.TMComp.prove_BJ
import Submission.Work.TMC16Core.Main.PLoc
import Submission.Work.TMC16Core.Bridge

/-!
# `prove_Loc`: C16 (Anderson localisation for large coupling) against the frozen contract

Target: `theorem prove_Loc : Work.TMContract.P_Loc`, i.e. AJ Thm 5.2 = Thm 9.1 (§9):
for irrational `α`, `b₀ ≥ 0`, `DiophBelow α b₀` and `λ > e^{16b₀/9}`, every generalized
eigenfunction decays exponentially for a.e. phase.

The proof is in `Submission/Work/TMC16Core/` (`Work.TMC16Core.*`), namespace
`Work.TMC16Core`:

* `Defs.lean` — vocabulary (verbatim copies of the contract's) and the AJ §9 objects
  (`dirMat`, `pd`, `G`, `IsRegular`, `IsRegularBig`, `AkSet`, `Uniform`, `Theta`,
  `RegFamily`, `P_RegFamily`, `ExpLocAEpos`).
* `Basic/reg_family.lean` — `reg_family : P_RegFamily` (the AJ §9 output, from
  `pd_window_core` + `green_bound_reg`).
* `Main/expLocAEpos_of_regFamily.lean` — patching: `P_RegFamily ⇒ ExpLocAEpos`.
* `Main/expLocAE_of_pos.lean` — reflection: one-sided decay ⇒ `ExpLocAE`.
* `Main/PLoc.lean` — `p_loc : P_UniqErg → P_OpBasics → P_LEBasics → P_BJ → P_Loc`.

`Bridge.lean` converts the frozen components C0, C1, C4, C7 into the local vocabulary
(the copies are byte-identical; `iterC`/`lyap` need an explicit induction bridge because
of `Nat.brecOn`).

**Status: the assembly is complete; the single remaining `sorry` of this component is
`Work.TMC16Core.Main.pd_window_reg` — whose statement is verbatim the body of `P_RegFamily`,
i.e. AJ §9's localisation core (Lemmas 9.4/9.5 with 9.6-9.13), see
`Submission/Work/TMC16Core/README.md`.**
-/

namespace Work.TMComp

theorem prove_Loc : Work.TMContract.P_Loc :=
  Work.TMC16Core.Main.p_loc Work.TMComp.prove_UniqErg Work.TMComp.prove_OpBasics
    ((Work.TMC16Core.Bridge.p_leBasics_iff).mpr Work.TMComp.prove_LEBasics)
    ((Work.TMC16Core.Bridge.p_bj_iff).mpr Work.TMComp.prove_BJ)

end Work.TMComp
