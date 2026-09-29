import Mathlib
import Submission.CDT.CintegralAssembled
import Submission.CDT.AintegralAssembled
import Submission.CDT.AintegralUntransformed
import Submission.CDT.SympExplicitodeFinal
import Submission.CDT.ZagierHBC

/-! Guidance from the project lead (the requester):

# Area Purge — make the reused Theorem-A side axiom-clean (no `native_decide`)
The seeded A-side modules use `native_decide` (175 occurrences: ZagierH, ZagierHBC, SympZagier,
EichlerInput, L2chi3Zagier, Cintegral*), which adds `…_native.native_decide.ax_*` axioms and
fails the permitted-axioms check. The statement bundles the A-side results the Theorem-A template
will reuse; all are already proved in the seed (`HA_ode`, `HB_ode`, `HC_ode` in ZagierH/ZagierHBC,
`GA_odeLHS_eq_zero` in SympExplicitodeFinal, `CintegralIdentity_proved` in CintegralAssembled,
`AintegralIdentity_proved` in AintegralAssembled, `overconvergesB_proved` (CintegralAssembled),
`overconvergesC_proved` (AintegralUntransformed)) — your job is that `#print axioms a_side_clean`
shows only propext/Classical.choice/Quot.sound.
Lead's axiom scan (2026-09-26): HB_ode, HC_ode, logP_*, Gdenominatortype, theoremA_iff_leaf are
ALREADY clean; HA_ode, GA_odeLHS_eq_zero, AintegralIdentity_proved are tainted ONLY through
`HA_coeff_zero/one/two` (ZagierH.lean lines 71–78, `native_decide`). Cintegral* not yet scanned
(check with `#print axioms` once built).
Method: EDIT THE SEEDED MODULES IN PLACE, PROOF-ONLY: replace each `native_decide` that the bundle
depends on by `decide`, `rfl`, `norm_num [HA_coeff, Finset.sum_range_succ, Nat.choose]`,
`simp`/`norm_num` with the definitions, or restructure. NEVER change a statement or a definition,
never delete lemmas (other agents import these modules). Leave `native_decide` in lemmas the bundle
does not depend on (report them). Cost-check kernel time of each replacement (`lake env lean` with
`set_option profiler true` on a scratch copy outside the workspace root) — big rational
evaluations (e.g. `HB_coeff 10 = 4308248502993/78400` in CintegralTen) should use a recurrence
evaluation that `decide`/`norm_num` handles, not a huge unfold.
Rebuilding downstream is HEAVY: the `Commons/Analysis/Summation/sum_cintegral*_core` modules take
5–17 GB each and ~20 min. Build only the modules you need, one `lake build <module>` at a time,
inside the solver's resource limits; do not launch parallel builds of the whole closure.
Then the proof of the bundle is `⟨HA_ode, HB_ode, HC_ode, GA_odeLHS_eq_zero, CintegralIdentity_proved,
AintegralIdentity_proved, overconvergesB_proved, overconvergesC_proved⟩`.
-/

namespace Work.Purge

theorem a_side_clean :
    Submission.CDT.HA_odeLHS Submission.CDT.HA = 0 ∧
    Submission.CDT.HA_odeLHS Submission.CDT.HB = 1 ∧
    Submission.CDT.HA_odeLHS Submission.CDT.HC = ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ ∧
    Submission.CDT.GA_odeLHS = 0 ∧
    Submission.CDT.CintegralIdentity ∧ Submission.CDT.AintegralIdentity ∧
    Submission.CDT.OverconvergesUnit Submission.CDT.eichlerDiffB ∧
    Submission.CDT.OverconvergesUnit Submission.CDT.eichlerDiffC :=
  ⟨Submission.CDT.HA_ode, Submission.CDT.HB_ode, Submission.CDT.HC_ode,
   Submission.CDT.GA_odeLHS_eq_zero,
   Submission.CDT.CintegralIdentity_proved, Submission.CDT.AintegralIdentity_proved,
   Submission.CDT.overconvergesB_proved, Submission.CDT.overconvergesC_proved⟩

end Work.Purge
