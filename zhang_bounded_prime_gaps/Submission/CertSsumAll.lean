import Submission.CertSsumRow0
import Submission.CertSsumRow1
import Submission.CertSsumRow2
import Submission.CertSsumRow3
import Submission.CertSsumRow4
import Submission.CertSsumRow5
import Submission.CertSsumRow6
import Submission.CertSsumRow7
import Submission.CertSsumRow8
import Submission.CertSsumRow9
import Submission.CertSsumRow10
import Submission.CertSsumRow11
import Submission.CertSsumRow12
import Submission.CertSsumRow13
import Submission.CertSsumRow14
import Submission.CertSsumRow15
import Submission.CertSsumRow16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-!
# Assembly of the `Ssum` table verification

`ssumTableL.getD i []` is the packed-DP row function `ssumRowOf` of the `i`-th signature group
`cSigs[i]`, assembled from the 17 chunk checks `Submission.CertSsumRow0 … CertSsumRow16`.
-/

namespace Commons.NumberTheory.MaynardSieve

theorem ssumTableL_row (i : ℕ) (hi : i < 272) :
    ssumTableL.getD i [] = ssumRowOf (cSigs.getD i cNil) := by
  obtain ⟨k, m, hk, hm, hikm⟩ : ∃ k m, k < 17 ∧ m < 16 ∧ i = 16 * k + m :=
    ⟨i / 16, i % 16, by omega, by omega, by omega⟩
  subst hikm
  interval_cases k
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_0 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_1 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_2 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_3 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_4 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_5 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_6 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_7 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_8 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_9 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_10 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_11 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_12 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_13 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_14 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_15 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp certRows_16 m (List.mem_range.mpr hm))

/-- Membership form of `ssumTableL_row`: for a pair in the zipped table, the second component is
the row function of the first. -/
theorem mem_zip_get {α β : Type*} {l : List α} {m : List β} {q : α × β}
    (h : q ∈ l.zip m) :
    ∃ i, ∃ (h₁ : i < l.length) (h₂ : i < m.length), l[i] = q.1 ∧ m[i] = q.2 := by
  induction l generalizing m with
  | nil => simp at h
  | cons a t ih =>
      cases m with
      | nil => simp at h
      | cons b u =>
          rw [List.zip_cons_cons, List.mem_cons] at h
          rcases h with h | h
          · cases h
            exact ⟨0, by simp, by simp, by simp, by simp⟩
          · obtain ⟨i, h₁, h₂, h₃, h₄⟩ := ih h
            refine ⟨i + 1, by simp [h₁], by simp [h₂], ?_, ?_⟩
            · simpa using h₃
            · simpa using h₄

theorem ssumTableL_mem {q : (List ℕ × List ℤ) × List ℕ} (h : q ∈ cSigs.zip ssumTableL) :
    q.2 = ssumRowOf q.1 := by
  obtain ⟨i, h₁, h₂, h₃, h₄⟩ := mem_zip_get h
  have hi : i < 272 := by rw [← cSigs_length]; exact h₁
  have hrow := ssumTableL_row i hi
  rw [List.getD_eq_getElem _ _ h₂, List.getD_eq_getElem _ _ h₁, h₃] at hrow
  rw [← h₄]
  exact hrow

theorem ssumTableL_mem' {q : (List ℕ × List ℤ) × List ℕ} (h : q ∈ cSigs.zip ssumTableL) :
    q.2 = cSigs.map (fun p => unpack (packedRow (mult q.1.1)) (mult p.1)) := by
  rw [ssumTableL_mem h]
  rfl

end Commons.NumberTheory.MaynardSieve
