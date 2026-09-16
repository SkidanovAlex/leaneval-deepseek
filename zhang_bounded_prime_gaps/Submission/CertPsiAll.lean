import Submission.CertPsiChunk0
import Submission.CertPsiChunk1
import Submission.CertPsiChunk2
import Submission.CertPsiChunk3
import Submission.CertPsiChunk4
import Submission.CertPsiChunk5
import Submission.CertPsiChunk6
import Submission.CertPsiChunk7
import Submission.CertPsiChunk8
import Submission.CertPsiChunk9
import Submission.CertPsiChunk10
import Submission.CertPsiChunk11
import Submission.CertPsiChunk12
import Submission.CertPsiChunk13
import Submission.CertPsiChunk14
import Submission.CertPsiChunk15
import Submission.CertPsiChunk16
import Submission.CertPsiChunk17

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The `J`-kernel as a table lookup

`certJPsiN j v j' v' = psiTab[N*51 + L]` with `N = certJN j v j' v' ≤ 52` and
`L = certJLM j v j' v' ≤ 50`, assembled from the 18 chunk checks of `psiTab`.
-/

namespace Commons.NumberTheory.MaynardSieve

theorem certJPsiN_eq_psiTab (j : Fin 1780) (v : ℕ) (hv : v ∈ (0 :: (certSig j).dedup).toFinset)
    (j' : Fin 1780) (v' : ℕ) (hv' : v' ∈ (0 :: (certSig j').dedup).toFinset) :
    certJPsiN j v j' v'
      = psiTab.getD ((certJN j v j' v') * 51 + (certJLM j v j' v')) 0 := by
  have hN : certJN j v j' v' ≤ 52 := certJN_le j v hv j' v' hv'
  have hL : certJLM j v j' v' ≤ 50 := certJLM_le j v j' v'
  obtain ⟨i, d, hi, hd, hNd⟩ : ∃ i d, i < 18 ∧ d < 3 ∧ certJN j v j' v' = 3 * i + d :=
    ⟨certJN j v j' v' / 3, certJN j v j' v' % 3, by omega, by omega, by omega⟩
  unfold certJPsiN
  rw [hNd]
  generalize hLdef : certJLM j v j' v' = L at hL ⊢
  have hL51 : L < 51 := by omega
  interval_cases i
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_0 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_1 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_2 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_3 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_4 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_5 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_6 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_7 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_8 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_9 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_10 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_11 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_12 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_13 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_14 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_15 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_16 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm
  · exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp psiTabSpec_17 d (List.mem_range.mpr hd)) L (List.mem_range.mpr hL51))).symm

end Commons.NumberTheory.MaynardSieve
