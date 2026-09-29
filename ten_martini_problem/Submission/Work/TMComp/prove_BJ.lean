import Submission.Work.TMContract.Components
import Submission.Work.TMC7Core.BJ
import Submission.Work.TMC7Core.Bridge.Components
import Submission.Work.TMC7Core.Bridge.P_BJ_transfer
import Submission.Work.TMC7Core.Scale.p_bj_of_dichotomy
import Submission.Work.TMComp.prove_OpBasics
import Submission.Work.TMComp.prove_LEBasics
import Submission.Work.TMComp.prove_Schnol

/-!
# `prove_BJ`: C7 (Bourgain–Jitomirskaya) against the frozen contract

Target: `theorem prove_BJ : Work.TMContract.P_BJ`, i.e. AJ Thm 2.1 = [BJ] Cor. 2:
for irrational `α`, `λ ≠ 0` and `E ∈ Σ_{λ,α}`, `L(E) = max 0 (log |λ|)`.

**Status: PROVED (2026-09-29), `sorry`-free and axiom-clean**
(`#print axioms Work.TMComp.prove_BJ` = `[propext, Classical.choice, Quot.sound]`).

The mathematical content lives in `Submission/Work/TMC7Core/` (`Work.TMC7Core.*`); everything in
the import closure of this file is `sorry`-free.  The proof is the dichotomy

```lean
theorem Work.TMC7Core.Scale.p_bj_of_dichotomy (h1 : P_OpBasics) (h4 : P_LEBasics)
    (h15 : P_Schnol) : P_BJ
```

(`Scale/p_bj_of_dichotomy.lean`) — Case I (`LiouvilleAbove α b*`) via `psi_upper` +
`psi_lower_rat` + `base_pairing_bd` + `liouville_approx` + `qsc` + `rat_bound_phase` +
`lipK_le_exp` + `lyapAvg_lipschitz`, Case II (`DiophBelow α b*`) via the proved Diophantine
case `Work.TMComp.RedC7T.D_BJ_dioph_of_tower` / `Scale.rat_tower_lower`.  Proposition 9 is
*not* used (the Prop. 9 statements of the plan were refuted by the fleet; see
`Submission/Work/TMC7Core/DESIGN.md` and `CHAPTER.md`).

The vocabulary of `Work.TMC7Core` is a byte-identical copy of the frozen `Work.TMContract`
definitions, but the two vocabularies are *not* definitionally equal (`rfl` fails, since the
definitions mention distinct constants); a bridge has to be proved by unfolding
(`iterC` by induction, `frob` by `simp only [frob, ...]`, then congruence).
-/

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp

theorem prove_BJ : Work.TMContract.P_BJ :=
  Work.TMC7Core.Bridge.P_BJ_transfer
    (Work.TMC7Core.Scale.p_bj_of_dichotomy
      (Work.TMC7Core.Bridge.P_OpBasics_transfer Work.TMComp.prove_OpBasics)
      (Work.TMC7Core.Bridge.P_LEBasics_transfer Work.TMComp.prove_LEBasics)
      (Work.TMC7Core.Bridge.P_Schnol_transfer Work.TMComp.prove_Schnol))

end Work.TMComp
