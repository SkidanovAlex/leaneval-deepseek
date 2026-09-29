import Submission.Work.TMComp.prove_mAnalytic
import Submission.Work.TMC13.Assembly

/-!
Component C13 (`P_FictLip`) of the Ten Martini formalisation.

The mathematics is assembled in `Submission/Work/TMC13/Assembly.lean`:

* `Work.TMC13.fictLip_of_mAnalytic : P_mAnalytic → P_FictLip` — the verified reduction
  (AJ Theorem 6.1).  From C9's conjugacy data `C`, `φ` on the spectral interval it builds the
  Prüfer lift calculus (`TMC13/Basic.lean`, `TMC13/Estimate.lean`), proves the existence of the
  Prüfer rotation number (C5 part 1, `TMC13/RotLiftLimit.prufer_rotLift_tendsto`, via Fekete's
  lemma), and derives the fictitious Lipschitz estimate
  `|N_{α'}(E) − N_α(E)| ≤ K|α' − α|` (`Estimate.rotLift_perturb`), including the far range via
  the 1-periodicity of `N` in the frequency (`Assembly.ids_add_int`).
  `#print axioms Work.TMC13.fictLip_of_mAnalytic` = `[propext, Classical.choice, Quot.sound]`.

* C9 (`Work.TMComp.prove_mAnalytic : Work.TMContract.P_mAnalytic`) supplies the conjugacy data;
  it is proved and axiom-clean, so this file is the two-line assembly above.

* The rescues and status notes for this directory are in
  `Submission/Work/TMC13/RESCUES.md` (§10.0–10.0b) and `Submission/Work/TMC13/NOTES.md`.
-/

namespace Work.TMComp

theorem prove_FictLip : Work.TMContract.P_FictLip :=
  Work.TMC13.fictLip_of_mAnalytic Work.TMComp.prove_mAnalytic

end Work.TMComp
