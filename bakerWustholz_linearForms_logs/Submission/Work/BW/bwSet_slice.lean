import Mathlib
import Submission.Work.BW.lcDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Slicing `bwSet` at the coordinate `k`: a point `Fin.insertNth k s y` lies in
`bwSet C k h u` iff its underlying slice point `y` lies in `C` (via `insertNth`) and,
for every `i`, `u i` lies in `[0, h i (y i)]`. -/
theorem bwSet_slice {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (s : ℝ) (u : Fin n → ℝ) :
    {y : Fin n → ℝ | Fin.insertNth k s y ∈ Work.BW.bwSet C k h u}
      = {y : Fin n → ℝ | Fin.insertNth k s y ∈ C ∧ ∀ i, 0 ≤ u i ∧ u i ≤ h i (y i)} := by
  by_cases hu : ∀ i, 0 ≤ u i
  · rw [bwSet_of_forall_nonneg _ _ _ hu]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hC, hb⟩
      exact ⟨hC, fun i => ⟨hu i, by simpa [Fin.insertNth_apply_succAbove] using hb i⟩⟩
    · rintro ⟨hC, hb⟩
      exact ⟨hC, fun i => by simpa [Fin.insertNth_apply_succAbove] using (hb i).2⟩
  · rw [bwSet_of_not _ _ _ hu]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, false_iff]
    intro hcon
    exact hu (fun i => (hcon.2 i).1)

end Work.BW
