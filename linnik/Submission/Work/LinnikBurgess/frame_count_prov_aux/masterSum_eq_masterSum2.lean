import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs

open scoped BigOperators

namespace Work.LinnikBurgess

/-- Reindexing: a sum over the box `s^3` (viewed as the `Finset` of functions `Fin 3 → ℕ`
taking values in `s`) equals the corresponding triple iterated sum. -/
lemma sum_piFinset_fin3 (s : Finset ℕ) (F : (Fin 3 → ℕ) → ℝ) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin 3 => s), F a)
      = ∑ x0 ∈ s, ∑ x1 ∈ s, ∑ x2 ∈ s, F ![x0, x1, x2] := by
  have key : (∑ a ∈ Fintype.piFinset (fun _ : Fin 3 => s), F a)
      = ∑ p ∈ s ×ˢ (s ×ˢ s), F ![p.1, p.2.1, p.2.2] := by
    refine Finset.sum_bij'
      (fun a _ => (a 0, (a 1, a 2)))
      (fun p _ => ![p.1, p.2.1, p.2.2]) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have ha' : ∀ i, a i ∈ s := Fintype.mem_piFinset.mp ha
      simp only [Finset.mem_product]
      exact ⟨ha' 0, ha' 1, ha' 2⟩
    · intro p hp
      rw [Fintype.mem_piFinset]
      have hp' : p.1 ∈ s ∧ p.2.1 ∈ s ∧ p.2.2 ∈ s := by
        simpa only [Finset.mem_product] using hp
      intro i
      fin_cases i <;> simp_all
    · intro a ha
      funext i
      fin_cases i <;> simp
    · intro a ha
      rcases a with ⟨a1, a2⟩
      rcases a2 with ⟨a21, a22⟩
      simp
    · intro a ha
      congr 1
      funext i
      fin_cases i <;> simp
  rw [key]
  simp only [Finset.sum_product]

end Work.LinnikBurgess

namespace Work.LinnikBurgess.frame_count_prov_aux

theorem masterSum_eq_masterSum2 (H m d g : ℕ) : masterSum H m d g = masterSum2 H m d g := by
  unfold masterSum masterSum2 box3
  simp only [Work.LinnikBurgess.sum_piFinset_fin3]

end Work.LinnikBurgess.frame_count_prov_aux
