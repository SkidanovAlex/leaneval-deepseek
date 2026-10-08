import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Group.odd_orderOf_mul
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two
import Submission.Work.BrauerSuzuki.Characters.sum_sum_char_eq
import Submission.Work.BrauerSuzuki.Q8.Cstar_Nstar_Astar
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.BrauerSuzuki.Q8.LamEta
import Submission.Work.BrauerSuzuki.Q8.Zeta
import Submission.Work.BrauerSuzuki.Q8.Eta
import Submission.Work.BrauerSuzuki.Q8.Eta2
import Submission.Work.BrauerSuzuki.Q8.GroupSetup
import Submission.Work.BrauerSuzuki.Q8.strongProved
import Submission.Work.BrauerSuzuki.Q8.Bset_facts
import Submission.Work.BrauerSuzuki.Q8.step3d_counting
import Submission.Work.BrauerSuzuki.Q8.step4a_ker_center
import Submission.Work.BrauerSuzuki.Q8.step4b_frobenius
import Submission.Work.BrauerSuzuki.Q8.step4b_center
import Submission.Work.BrauerSuzuki.Q8.step6_inner_eta
import Submission.Work.BrauerSuzuki.Q8.step6_inner_eta_classfun
import Submission.Work.BrauerSuzuki.Q8.step7a_values_int
import Submission.Work.BrauerSuzuki.Q8.step7b_values_conj
import Submission.Work.BrauerSuzuki.Q8.step8_odd
import Submission.Work.BrauerSuzuki.Q8.step9_chi_x
import Submission.Work.BrauerSuzuki.Q8.step9_deg_two
import Submission.Work.BrauerSuzuki.Q8.step10_character_congruences
import Submission.Work.BrauerSuzuki.Characters.vchar_of_norm_four
import Submission.Work.BrauerSuzuki.Arith.glauberman_step11
import Submission.Work.BrauerSuzuki.Sylow.genQuaternionData_quotient_oddCore
import Submission.Work.ThreePoints.oddCore_quotient_oddCore
import Submission.Work.NPC.All
import Submission.Work.BrauerSuzuki.Q8.Assembly

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

-- Glauberman 1974 (Illinois J. Math. 18, 60-65), the `|S| = 8` case of Brauer-Suzuki in the
-- strong form `|Z(G/O(G))| = 2`.  See REFS/brauer_suzuki.md section 3, the authoritative
-- transcription REFS/vision/glauberman1974/, and Gorenstein, Finite Groups, Chapter 12
-- (adapting Lemmas 12.1.2-12.1.8).  Steps (1)-(11) of the source; step (1) is
-- `Q8/Cstar_Nstar_Astar`; for the counting steps (3)(d) and (8),(9) use
-- `Group/odd_orderOf_mul` (no element of `B` is a product of two involutions, Gorenstein
-- 12.1.7) and `Characters/sum_sum_char_eq`; step (4) uses the `|S| > 8` case
-- (`Dade/main`) and Frobenius' normal 2-complement theorem (`Work.NPC.frobenius_npc`);
-- step (7) uses the Galois action on `Irr` (`Work.Clifford.galoisChar_mem_Irr`).
theorem main : Work.BrauerSuzuki.BrauerSuzukiQ8Strong := fun G _ _ S d h2 t ht g =>
  main_aux (Nat.card G) G rfl S d h2 t ht g

end Work.BrauerSuzuki.Q8
