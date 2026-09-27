import Mathlib
import Submission.Work.Cohomology.EZShuffleGen

namespace Work.Cohomology.EZG

theorem cnt_cross {n : ℕ} (A : Finset (Fin (n + 1))) (q : Fin n)
    (hq : q.castSucc ∈ A) (hq' : q.succ ∈ A) (j : Fin n) :
    cnt (delPosP A q.succ) j.val ≥ cnt A q.succ.val ↔ (q : ℕ) < (j : ℕ) := by
  have hqv : (q.succ : Fin (n+1)).val = (q : ℕ) + 1 := Fin.val_succ q
  -- If `j` is below (or at) `q`, then `cnt (delPosP A q.succ) j` is at most `cnt A j`.
  have key1 (hle : (j:ℕ) ≤ (q:ℕ)) : cnt (delPosP A q.succ) j.val ≤ cnt A j.val := by
    rw [cnt, cnt]
    refine Finset.card_le_card_of_injOn (fun t : Fin n => Fin.succAbove q.succ t) ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_coe] at ht ⊢
      obtain ⟨htS, htj⟩ := ht
      refine ⟨mem_delPosP.mp htS, ?_⟩
      have htq : t ≤ q := by rw [Fin.le_iff_val_le_val]; omega
      rw [Fin.succAbove_succ_of_le q t htq, Fin.val_castSucc]
      exact htj
    · intro t1 _ t2 _ h
      exact Fin.succAbove_right_injective h
  -- If `q < j`, then `cnt A q.succ` is at most `cnt (delPosP A q.succ) j`.
  have key2 (hlt : (q:ℕ) < (j:ℕ)) : cnt A q.succ.val ≤ cnt (delPosP A q.succ) j.val := by
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    rw [cnt, cnt]
    refine Finset.card_le_card_of_injOn
      (fun i : Fin (n+1) => if h : i.val < n then ⟨i.val, h⟩ else ⟨0, hn⟩) ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_coe] at hi ⊢
      obtain ⟨hiA, hiv⟩ := hi
      have hN : i.val < n := by omega
      rw [dif_pos hN]
      refine ⟨?_, ?_⟩
      · rw [mem_delPosP]
        have hleq : (⟨i.val, hN⟩ : Fin n) ≤ q := by
          rw [Fin.le_iff_val_le_val]
          show i.val ≤ q.val
          omega
        rw [Fin.succAbove_succ_of_le q ⟨i.val, hN⟩ hleq]
        have hh : (⟨i.val, hN⟩ : Fin n).castSucc = i := Fin.ext rfl
        rw [hh]; exact hiA
      · show i.val < j.val; omega
    · intro i1 hi1 i2 hi2 h
      simp only [Finset.mem_filter, Finset.mem_coe] at hi1 hi2
      have hN1 : i1.val < n := by omega
      have hN2 : i2.val < n := by omega
      simp only [hN1, hN2, ↓reduceDIte] at h
      exact Fin.ext (by simpa only [Fin.mk.injEq] using h)
  constructor
  · intro hS
    rcases lt_or_ge (q:ℕ) (j:ℕ) with hlt | hge
    · exact hlt
    · exfalso
      have h1 : cnt (delPosP A q.succ) j.val ≤ cnt A j.val := key1 hge
      have h2 : cnt A j.val < cnt A q.succ.val := by
        rw [hqv]
        exact cnt_lt_cnt A (by omega) q.castSucc hq (by simpa using hge) (by simp)
      omega
  · intro hlt
    exact key2 hlt

end Work.Cohomology.EZG
