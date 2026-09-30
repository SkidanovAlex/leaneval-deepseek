import Mathlib
import Submission.Work.BW.lcDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem bwSet_neg {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (hh_even : ∀ i x, h i (-x) = h i x) (hsym : C = -C) (u : Fin n → ℝ) :
    Work.BW.bwSet C k h u = -Work.BW.bwSet C k h u := by
  -- Negation fixes `C` (by hypothesis) and fixes each of the level sets of `h`
  -- (because `h` is even), hence fixes the whole `bwSet`.
  have hCsym : ∀ w : Fin (n+1) → ℝ, (-w ∈ C ↔ w ∈ C) := by
    intro w
    calc -w ∈ C ↔ w ∈ -C := Set.mem_neg.symm
      _ ↔ w ∈ C := (Set.ext_iff.mp hsym w).symm
  have hAsym : ∀ (i : Fin n) (w : Fin (n+1) → ℝ),
      (-w ∈ {z : Fin (n+1) → ℝ | u i ≤ h i (z (k.succAbove i))}
        ↔ w ∈ {z : Fin (n+1) → ℝ | u i ≤ h i (z (k.succAbove i))}) := by
    intro i w
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, hh_even]
  rcases em (∀ i, 0 ≤ u i) with hu | hu
  · rw [bwSet_of_forall_nonneg C k h hu]
    ext w
    simp only [Set.mem_neg, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hc, hA⟩
      exact ⟨(hCsym w).mpr hc, fun i => (hAsym i w).mpr (hA i)⟩
    · rintro ⟨hc, hA⟩
      exact ⟨(hCsym w).mp hc, fun i => (hAsym i w).mp (hA i)⟩
  · rw [bwSet_of_not C k h hu]
    simp

end Work.BW
