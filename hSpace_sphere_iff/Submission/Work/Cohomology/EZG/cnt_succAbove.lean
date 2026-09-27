import Mathlib
import Submission.Work.Cohomology.EZShuffleGen

namespace Work.Cohomology.EZG

/-- The value of `Fin.succAbove`, as an explicit `if`. -/
lemma val_succAbove_aux {n : ℕ} (p : Fin (n+1)) (i : Fin n) :
    ((Fin.succAbove p i : Fin (n+1)) : ℕ) = if (i:ℕ) < (p:ℕ) then (i:ℕ) else (i:ℕ)+1 := by
  by_cases h : (i:ℕ) < (p:ℕ)
  · rw [Fin.succAbove_of_castSucc_lt p i
        (by simp only [Fin.lt_def, Fin.val_castSucc]; exact h), Fin.val_castSucc, if_pos h]
  · rw [Fin.succAbove_of_le_castSucc p i
        (by simp only [Fin.le_def, Fin.val_castSucc]; omega), Fin.val_succ, if_neg h]

/-- `p` is strictly below `p.succAbove j` exactly when `p` is not to the right of `j`. -/
lemma lt_val_succAbove_iff {n : ℕ} (p : Fin (n+1)) (j : Fin n) :
    (p:ℕ) < (Fin.succAbove p j : ℕ) ↔ (p:ℕ) ≤ (j:ℕ) := by
  rw [val_succAbove_aux]
  by_cases h : (j:ℕ) < (p:ℕ)
  · rw [if_pos h]; constructor <;> intro hh <;> omega
  · rw [if_neg h]; constructor <;> intro hh <;> omega

/-- Counting the elements of `A : Finset (Fin (n+1))` below `p.succAbove j` reduces to counting
the elements of `delPosP A p` below `j`, plus a possible contribution of `p` itself. -/
lemma card_filter_lt_succAbove {n : ℕ} (A : Finset (Fin (n+1))) (p : Fin (n+1)) (j : Fin n) :
    (A.filter (fun i : Fin (n+1) => (i:ℕ) < (Fin.succAbove p j : ℕ))).card
      = ((delPosP A p).filter (fun t : Fin n => (t:ℕ) < (j:ℕ))).card
        + (if p ∈ A ∧ (p:ℕ) ≤ (j:ℕ) then 1 else 0) := by
  set S := A.filter (fun i : Fin (n+1) => (i:ℕ) < (Fin.succAbove p j : ℕ)) with hSdef
  set T := (delPosP A p).filter (fun t : Fin n => (t:ℕ) < (j:ℕ)) with hTdef
  have hmemS : ∀ i : Fin (n+1), i ∈ S ↔ i ∈ A ∧ (i:ℕ) < (Fin.succAbove p j : ℕ) := by
    intro i; rw [hSdef]; simp only [Finset.mem_filter]
  have hmemT : ∀ t : Fin n, t ∈ T ↔ t ∈ delPosP A p ∧ (t:ℕ) < (j:ℕ) := by
    intro t; rw [hTdef]; simp only [Finset.mem_filter]
  have hcard' : T.card = (S.erase p).card := by
    refine Finset.card_bij (fun (t : Fin n) (_ : t ∈ T) => Fin.succAbove p t) ?_ ?_ ?_
    · intro t ht
      rw [Finset.mem_erase, hmemS]
      refine ⟨Fin.succAbove_ne p t, ?_, ?_⟩
      · exact mem_delPosP.mp ((hmemT t).mp ht).1
      · have htlt : (t:ℕ) < (j:ℕ) := ((hmemT t).mp ht).2
        exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mpr (Fin.lt_def.mpr htlt))
    · intro t1 _ t2 _ h
      exact Fin.succAbove_right_injective h
    · intro b hb
      rw [Finset.mem_erase, hmemS] at hb
      obtain ⟨hbne, hbA, hblt⟩ := hb
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hbne
      refine ⟨t, ?_, ht⟩
      rw [hmemT]
      refine ⟨mem_delPosP.mpr (ht.symm ▸ hbA), ?_⟩
      have h1 : Fin.succAbove p t < Fin.succAbove p j := ht.symm ▸ Fin.lt_def.mp hblt
      exact Fin.lt_def.mp (Fin.succAbove_lt_succAbove_iff.mp h1)
  have hcard : (S.erase p).card = T.card := hcard'.symm
  have hpS : p ∈ S ↔ p ∈ A ∧ (p:ℕ) ≤ (j:ℕ) := by
    rw [hmemS]
    exact and_congr_right (fun _ => lt_val_succAbove_iff p j)
  have hsplit : (S.erase p).card + (if p ∈ S then 1 else 0) = S.card := by
    by_cases hp : p ∈ S
    · rw [if_pos hp]; exact Finset.card_erase_add_one hp
    · rw [if_neg hp, add_zero, Finset.erase_eq_self.mpr hp]
  rw [← hsplit, hcard]
  simp only [hpS]

theorem cnt_succAbove {n : ℕ} (A : Finset (Fin (n + 1))) (p : Fin (n + 1)) (j : Fin n) :
    cnt A (Fin.succAbove p j).val
      = cnt (delPosP A p) j.val + (if p ∈ A ∧ (p : ℕ) ≤ (j : ℕ) then 1 else 0) := by
  simpa only [cnt] using card_filter_lt_succAbove A p j

end Work.Cohomology.EZG
