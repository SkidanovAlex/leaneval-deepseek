import Mathlib
import Submission.Work.BMF.adi_all_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- For `j : Fin ℓ`, `{j' : Fin ℓ | j'.val < j.val + 1} = {j} ∪ {j' | j'.val < j.val}`. -/
private lemma filter_lt_succ_eq_insert (ℓ : ℕ) (j : Fin ℓ) :
    (Finset.univ.filter (fun j' : Fin ℓ => j'.val < j.val + 1)) =
      insert j (Finset.univ.filter (fun j' : Fin ℓ => j'.val < j.val)) := by
  ext j'
  simp only [mem_insert, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have h' : j'.val ≤ j.val := by omega
    rcases lt_or_eq_of_le h' with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl (Fin.ext heq)
  · rintro (rfl | h)
    · omega
    · omega

/-- For `j : Fin ℓ`, `{j' : Fin ℓ | j.val ≤ j'.val} = {j} ∪ {j' | j.val < j'.val}`. -/
private lemma filter_le_eq_insert (ℓ : ℕ) (j : Fin ℓ) :
    (Finset.univ.filter (fun j' : Fin ℓ => j.val ≤ j'.val)) =
      insert j (Finset.univ.filter (fun j' : Fin ℓ => j.val < j'.val)) := by
  ext j'
  simp only [mem_insert, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl (Fin.ext heq.symm)
  · rintro (rfl | h)
    · omega
    · omega

/-- `{j' : Fin ℓ | j.val + 1 ≤ j'.val} = {j' | j.val < j'.val}` for `j : Fin ℓ`. -/
private lemma filter_succ_le_eq (ℓ : ℕ) (j : Fin ℓ) :
    (Finset.univ.filter (fun j' : Fin ℓ => j.val + 1 ≤ j'.val)) =
      (Finset.univ.filter (fun j' : Fin ℓ => j.val < j'.val)) := by
  ext j'
  simp only [mem_filter, mem_univ, true_and]
  omega

theorem cycFac_basic (ℓ : ℕ) (V U : Fin ℓ → ℕ) (hV : ∀ j, 0 < V j) (hU : ∀ j, 0 < U j) :
    (Work.BMF.cycFac ℓ V U 0 = ∏ j' : Fin ℓ, V j') ∧
    (Work.BMF.cycFac ℓ V U ℓ = ∏ j' : Fin ℓ, U j') ∧
    (∀ j : Fin ℓ, Work.BMF.aaV ℓ V U j * V j = Work.BMF.cycFac ℓ V U j.val) ∧
    (∀ j : Fin ℓ, Work.BMF.aaV ℓ V U j * U j = Work.BMF.cycFac ℓ V U (j.val + 1)) ∧
    (∀ j : ℕ, 0 < Work.BMF.cycFac ℓ V U j) ∧
    (∀ j : Fin ℓ, 0 < Work.BMF.aaV ℓ V U j) := by
  have hP0 : (Finset.univ.filter (fun j' : Fin ℓ => j'.val < 0)) = ∅ := by simp
  have hQ0 : (Finset.univ.filter (fun j' : Fin ℓ => 0 ≤ j'.val)) = Finset.univ := by simp
  have hPl : (Finset.univ.filter (fun j' : Fin ℓ => j'.val < ℓ)) = Finset.univ := by
    exact Finset.filter_true_of_mem (fun x _ => x.isLt)
  have hQl : (Finset.univ.filter (fun j' : Fin ℓ => ℓ ≤ j'.val)) = ∅ := by
    exact Finset.filter_false_of_mem (fun x _ => not_le.mpr x.isLt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cycFac, hP0, hQ0, Finset.prod_empty, one_mul]
  · rw [cycFac, hPl, hQl, Finset.prod_empty, mul_one]
  · intro j
    rw [cycFac, aaV, filter_le_eq_insert]
    have hj : j ∉ Finset.univ.filter (fun j' : Fin ℓ => j.val < j'.val) := by simp
    rw [Finset.prod_insert hj]
    ring
  · intro j
    rw [cycFac, aaV, filter_lt_succ_eq_insert, filter_succ_le_eq]
    have hj : j ∉ Finset.univ.filter (fun j' : Fin ℓ => j'.val < j.val) := by simp
    rw [Finset.prod_insert hj]
    ring
  · intro j
    rw [cycFac]
    exact mul_pos (Finset.prod_pos fun i _ => hU i) (Finset.prod_pos fun i _ => hV i)
  · intro j
    rw [aaV]
    exact mul_pos (Finset.prod_pos fun i _ => hU i) (Finset.prod_pos fun i _ => hV i)

end Work.BMF
