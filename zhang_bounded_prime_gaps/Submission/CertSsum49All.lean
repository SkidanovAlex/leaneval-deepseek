import Submission.CertSsum49Row0
import Submission.CertSsum49Row1
import Submission.CertSsum49Row2
import Submission.CertSsum49Row3
import Submission.CertSsum49Row4
import Submission.CertSsum49Row5
import Submission.CertSsum49Row6
import Submission.CertSsum49Row7
import Submission.CertSsum49Row8
import Submission.CertSsum49Row9
import Submission.CertSsum49Row10
import Submission.CertSsum49Row11
import Submission.CertSsum49Row12
import Submission.CertSsum49Row13
import Submission.CertSsum49Row14
import Submission.CertSsum49Row15
import Submission.CertSsum49Row16
import Submission.CertSsumAll

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-!
# Assembly of the `k = 49` table verification

`ssumTable49L.getD i []` is the packed row DP at level `49` of the `i`-th signature group,
assembled from the 17 chunk checks `Submission.CertSsum49Row0 … CertSsum49Row16`.
-/

namespace Commons.NumberTheory.MaynardSieve

theorem ssumTable49L_row (i : ℕ) (hi : i < 272) :
    ssumTable49L.getD i [] = ssumRowOfAt 49 (cSigs.getD i cNil) := by
  obtain ⟨k, m, hk, hm, hikm⟩ : ∃ k m, k < 17 ∧ m < 16 ∧ i = 16 * k + m :=
    ⟨i / 16, i % 16, by omega, by omega, by omega⟩
  subst hikm
  interval_cases k
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_0 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_1 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_2 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_3 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_4 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_5 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_6 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_7 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_8 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_9 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_10 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_11 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_12 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_13 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_14 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_15 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows49_16 m (List.mem_range.mpr hm))

theorem ssumTable49L_mem {q : (List ℕ × List ℤ) × List ℕ} (h : q ∈ cSigs.zip ssumTable49L) :
    q.2 = ssumRowOfAt 49 q.1 := by
  obtain ⟨i, h₁, h₂, h₃, h₄⟩ := mem_zip_get h
  have hi : i < 272 := by rw [← cSigs_length]; exact h₁
  have hrow := ssumTable49L_row i hi
  rw [List.getD_eq_getElem _ _ h₂, List.getD_eq_getElem _ _ h₁, h₃] at hrow
  rw [← h₄]
  exact hrow

theorem ssumTable49L_mem' {q : (List ℕ × List ℤ) × List ℕ} (h : q ∈ cSigs.zip ssumTable49L) :
    q.2 = cSigs.map (fun p => unpack (packedRowAt 49 (mult q.1.1)) (mult p.1)) := by
  rw [ssumTable49L_mem h]
  rfl

end Commons.NumberTheory.MaynardSieve
