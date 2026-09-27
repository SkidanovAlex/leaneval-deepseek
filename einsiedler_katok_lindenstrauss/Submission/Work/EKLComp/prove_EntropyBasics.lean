import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLComp.HPE2
import Submission.Work.EKLComp.ent_conj
import Submission.Work.EKLComp.ent_inverse
import Submission.Work.EKLComp.ent_affine
import Submission.Work.EKLComp.ent_generating
import Submission.Work.EKLComp.ent_pow
import Submission.Work.EKLComp.ent_jacobs

/-!
# C3 — Kolmogorov–Sinai entropy basics: the component `P_EntropyBasics` (FROZEN)

Assembled from the seven clauses of `P_EntropyBasics`:
* (E1) `Work.EKLComp.ent_inverse`           — inverses have equal entropy;
* (E2) `Work.EKLComp.ent_conj`              — conjugacy invariance;
* (E3) `Work.EKLComp.ent_affine`            — affinity;
* (E4) `Work.EKLComp.ent_generating`        — generating sequences;
* (E5) `Work.EKLComp.Core.hPart_eq_Hcond`   — the conditional-entropy formula (proved here);
* (E6) `Work.EKLComp.ent_pow`               — powers;
* (E7) `Work.EKLComp.ent_jacobs`            — Jacobs' theorem.

The foundation used by (E5) and by the fleet lives in
`Work.EKLComp.Core` (`Core`, `Entropy`, `Hcond`, `HPE`, `HPE3`, `HPE2`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLComp

theorem prove_EntropyBasics : Work.EKLContract.P_EntropyBasics := by
  intro X mX μ μprob
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ent_inverse μ
  · exact ent_conj μ
  · exact ent_affine μ
  · exact ent_generating μ
  · intro T hT hmp P
    rw [Work.EKLComp.Core.hPart_eq_Hcond μ hmp P, Work.EKLComp.Core.mInf]
  · exact ent_pow μ
  · exact ent_jacobs μ

end Work.EKLComp
