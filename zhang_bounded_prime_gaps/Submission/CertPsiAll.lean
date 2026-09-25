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

/-- An entry of `psiTab` from the slice check of its chunk. -/
theorem psiTab_entry_of_slice (i d L : ℕ) (hd : d < 3) (hL : L < 51)
    (h : (psiTab.drop (153 * i)).take 153
      = (List.range 153).map (fun t => ∑ jj ∈ Finset.range ((3 * i + t / 51) + 1),
          certJPsiTermN (3 * i + t / 51) (t % 51) jj)) :
    psiTab.getD ((3 * i + d) * 51 + L) 0
      = ∑ jj ∈ Finset.range ((3 * i + d) + 1), certJPsiTermN (3 * i + d) L jj := by
  have ht : 51 * d + L < 153 := by omega
  have hidx : (3 * i + d) * 51 + L = 153 * i + (51 * d + L) := by ring
  have hdiv : (51 * d + L) / 51 = d := by omega
  have hmod : (51 * d + L) % 51 = L := by omega
  have key := congrArg (fun l : List ℕ => l.getD (51 * d + L) 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range ht, Option.map_some, Option.getD_some, ht,
    if_true, hdiv, hmod] at key
  rw [hidx, List.getD_eq_getElem?_getD]
  exact key

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
  · exact (psiTab_entry_of_slice 0 d L hd hL51 psiTabSlice_0).symm
  · exact (psiTab_entry_of_slice 1 d L hd hL51 psiTabSlice_1).symm
  · exact (psiTab_entry_of_slice 2 d L hd hL51 psiTabSlice_2).symm
  · exact (psiTab_entry_of_slice 3 d L hd hL51 psiTabSlice_3).symm
  · exact (psiTab_entry_of_slice 4 d L hd hL51 psiTabSlice_4).symm
  · exact (psiTab_entry_of_slice 5 d L hd hL51 psiTabSlice_5).symm
  · exact (psiTab_entry_of_slice 6 d L hd hL51 psiTabSlice_6).symm
  · exact (psiTab_entry_of_slice 7 d L hd hL51 psiTabSlice_7).symm
  · exact (psiTab_entry_of_slice 8 d L hd hL51 psiTabSlice_8).symm
  · exact (psiTab_entry_of_slice 9 d L hd hL51 psiTabSlice_9).symm
  · exact (psiTab_entry_of_slice 10 d L hd hL51 psiTabSlice_10).symm
  · exact (psiTab_entry_of_slice 11 d L hd hL51 psiTabSlice_11).symm
  · exact (psiTab_entry_of_slice 12 d L hd hL51 psiTabSlice_12).symm
  · exact (psiTab_entry_of_slice 13 d L hd hL51 psiTabSlice_13).symm
  · exact (psiTab_entry_of_slice 14 d L hd hL51 psiTabSlice_14).symm
  · exact (psiTab_entry_of_slice 15 d L hd hL51 psiTabSlice_15).symm
  · exact (psiTab_entry_of_slice 16 d L hd hL51 psiTabSlice_16).symm
  · exact (psiTab_entry_of_slice 17 d L hd hL51 psiTabSlice_17).symm

end Commons.NumberTheory.MaynardSieve
