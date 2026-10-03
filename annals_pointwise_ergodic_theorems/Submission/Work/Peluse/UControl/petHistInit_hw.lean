import Mathlib
import Submission.Work.Peluse.UControl.HistInv
import Submission.Work.Peluse.UControl.petInitSym_hw

/-!
# The window condition at the initial history state

The `hw` field of `HistInv` at `⟨0, petHistInit P hd⟩` with the window `petWindow γ D n`,
`n = histLen ⟨0, petHistInit P hd⟩`: a verbatim copy of `petInitSym_hw` (the condition is
*decreasing* in the step count, and `petWindow` is its value at the last step).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

/-- The window radius `petWindow γ D (histLen ⟨0, petHistInit P hd⟩)` satisfies the window condition
of `HistInv` at every step of the history chain. -/
theorem petHistInit_hw (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (γ : ℝ) (D : ℕ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hD : 1 ≤ D) :
    ∀ k : ℕ, k < histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree) →
      petWindow γ D (histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree)) ≤
        petChainLevel γ k ^ 2 / (20000 * (((2 ^ k * D : ℕ) : ℝ) + 1)) := by
  intro k hk
  have hk' : k ≤ histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree) - 1 :=
    Nat.le_sub_one_of_lt hk
  have hmono := petChainWindowLevel_antitone γ D hγ0 hγ1 hk'
  calc petWindow γ D (histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree))
      = min 1 (petChainLevel γ (histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree) - 1) ^ 2
          / (20000 * (((2 ^ (histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree) - 1) * D : ℕ)
              : ℝ) + 1))) := rfl
    _ ≤ petChainLevel γ (histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree) - 1) ^ 2
          / (20000 * (((2 ^ (histLen (⟨0, petHistInit P hd⟩ : HState P.natDegree) - 1) * D : ℕ)
              : ℝ) + 1)) := min_le_right _ _
    _ ≤ petChainLevel γ k ^ 2 / (20000 * (((2 ^ k * D : ℕ) : ℝ) + 1)) := hmono

end

end Work.Peluse.UControl
