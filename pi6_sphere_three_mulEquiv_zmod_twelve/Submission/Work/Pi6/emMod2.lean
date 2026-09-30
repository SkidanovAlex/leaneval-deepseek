import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.Final
import Submission.Work.Pi6.EMM2.k2forcing9
import Submission.Work.Pi6.EMM2.k3forcing9
import Submission.Work.Pi6.EMM2.k4forcing9
import Submission.Work.Pi6.EMM2.kZmodelLow
import Submission.Work.Pi6.EMM2.k2fieldLow
import Submission.Work.Pi6.EMM2.finiteType
import Submission.Work.Pi6.EMM2.lowDegree
import Submission.Work.Pi6.EMM2.secondCohZModTwo
import Submission.Work.Pi6.EMM2.mulComm
import Submission.Work.Pi6.EMM2.cupOne
import Submission.Work.Pi6.EMM2.pathFib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port


/-! Guidance from the project lead (the requester):

AREA EMM2 (pi6). Read REFS/NOTES_LEAD_PI6.md §4 (the K(ℤ/2,2), K(ℤ/2,3), K(ℤ/2,4) parts: every differential is written
out there). Assume MSSHolds (hM) and K2ZFacts (hZ). All cohomology mod 2.
Statement: K(ℤ/2,2) models: rank H^3 ≤ 1, a ≠ 0 in H^2 ⇒ a² ≠ 0, y ≠ 0 in H^3 ⇒ y² ≠ 0. K(ℤ/2,3): rank H^4, H^5 ≤ 1,
a ≠ 0 in H^3 ⇒ a² ≠ 0. K(ℤ/2,4): rank H^7 ≤ 2, rank H^8 ≤ 2. (Range models through N ≥ 10.)
K(ℤ/2,2) — use the fibration of r : Kℤ → X, NOT the path fibration: build Kℤ from S² by iterated Work.Serre.KillCells
(a K(ℤ,2) model), r = extension of a generator S² → X over the cells (Work.EMFG.killCellsExtend; X has π_i = 0 for
2 < i ≤ N). mpathQ r : mpath r → X, total ≃ Kℤ (Work.FGThm.mpathHomotopyEquiv), fibre F = hofib r is a K(ℤ,2) and
F → Kℤ is ×2 on π_2 = H_2, hence 0 on H^{>0}(−;𝔽₂) (cup powers of the generator, K2ZFacts). So E_∞^{0,q} = 0 (q > 0,
edge_fibre) and the E_∞ total dimensions are 1,0,1,0,1,... (conv_dim with K2ZFacts). Then (NOTES): d_3 w = y_3 spans H^3;
ι² ≠ 0 because r is onto on H_2 so r^*ι = z and r^*(ι²) = z² ≠ 0; d_3(w²) = 2wy_3 = 0 so y_3·w is never hit and must die,
d_3(y_3 w) = y_3² ≠ 0. Also record (internally) rank H^4 ≤ 1, H^5 ≤ 2, H^6 ≤ 2, H^7 ≤ 2 and ιy_3 ≠ 0, ι³ ≠ 0.
K(ℤ/2,3), K(ℤ/2,4): path fibrations (fibre = loops = K(ℤ/2,n−1) through N−1); follow NOTES §4 line by line.
Graded commutativity of products on E_r is not a field of CohSS: derive it from e2_mul + Work.Cohomology.gradedComm
+ proj_mul/proj_surj (char 2: signs vanish).
Prove the three forcing lemmas for models through N ≥ 8 (K2), ≥ 9 (K3), ≥ 10 (K4) internally: loops lower N by one.
Suggested children: Pi6/EMM2/kZmodel (Kℤ and r), Pi6/EMM2/k2forcing, Pi6/EMM2/k3forcing, Pi6/EMM2/k4forcing,
Pi6/EMM2/finiteType (shared with K2Z: import theirs if it exists).
NOT needed: Steenrod squares, Kudo, test spaces, full cohomology rings, exact dimensions beyond the stated bounds.
-/

namespace Work.Pi6

theorem emMod2 (hM : Work.Pi6.MSSHolds) (hZ : Work.Pi6.K2ZFacts) : Work.Pi6.EMMod2 :=
  Work.Pi6.EMM2.emMod2_assembly hM hZ
    Work.Pi6.EMM2.k2forcing9 Work.Pi6.EMM2.k3forcing9 Work.Pi6.EMM2.k4forcing9
    Work.Pi6.EMM2.kZmodelLow Work.Pi6.EMM2.finiteType Work.Pi6.EMM2.lowDegree
    Work.Pi6.EMM2.k2fieldLow Work.Pi6.EMM2.secondCohZModTwo Work.Pi6.EMM2.mulComm
    Work.Pi6.EMM2.cupOne Work.Pi6.EMM2.pathFib

end Work.Pi6
