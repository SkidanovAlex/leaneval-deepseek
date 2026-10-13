import Mathlib
import Submission.Work.WilG1.Basic

namespace Work.WilG1.Choice

theorem cylDecomp_cell_of_mem {n : ℕ} {C : Finset (Set (Fin n → ℝ))} {X : Set (Fin n → ℝ)}
    (hC : WilkiesDesign.IsCylDecomp n C) (hcomp : ∀ κ ∈ C, κ ⊆ X ∨ Disjoint κ X)
    {z : Fin n → ℝ} (hz : z ∈ X) : ∃ κ ∈ C, κ ⊆ X ∧ z ∈ κ := by
  -- `C` covers all of `ℝⁿ`: in dimension `0` it is the singleton `{univ}`, and in
  -- dimension `n+1` this is the third conjunct of `IsCylDecomp`.
  have cov : ∀ z : Fin n → ℝ, ∃ c ∈ C, z ∈ c := by
    cases n with
    | zero =>
      intro z
      rw [hC]
      exact ⟨Set.univ, by simp, trivial⟩
    | succ m => exact hC.2.2.1
  obtain ⟨c, hcC, hzc⟩ := cov z
  -- the cell containing `z` cannot be disjoint from `X`, since `z` lies in both.
  rcases hcomp c hcC with hsub | hdisj
  · exact ⟨c, hcC, hsub, hzc⟩
  · exact absurd hz (Set.disjoint_left.mp hdisj hzc)

end Work.WilG1.Choice
