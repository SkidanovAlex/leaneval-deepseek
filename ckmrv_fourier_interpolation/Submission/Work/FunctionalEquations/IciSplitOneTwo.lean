import Mathlib
import Submission.Work.FunctionalEquations.Basic

namespace Work.FunctionalEquations

set_option linter.unusedVariables false in
/-- Splitting off the `m = 1` term of a sum over `Set.Ici 1`, using that
`f` vanishes there.  The inclusion `Set.Ici 2 ↪ Set.Ici 1` has range exactly
the points different from `1`, and `f` is supported on that range. -/
theorem IciSplitOneTwo {f : Set.Ici (1 : ℕ) → ℂ} (hf : Summable f)
    (h0 : f ⟨1, by simp⟩ = 0) :
    (∑' m : Set.Ici (1 : ℕ), f m) = ∑' m : Set.Ici (2 : ℕ),
      f ⟨m.1, Set.mem_Ici.mpr (le_trans (by norm_num) (Set.mem_Ici.mp m.2))⟩ := by
  -- the inclusion `Set.Ici 2 ↪ Set.Ici 1`
  let g : Set.Ici (2 : ℕ) → Set.Ici (1 : ℕ) :=
    fun m => ⟨m.1, Set.mem_Ici.mpr (le_trans (by norm_num) (Set.mem_Ici.mp m.2))⟩
  have hinj : Function.Injective g := by
    intro m n hmn
    have h1 : m.1 = n.1 := by simpa [g] using congrArg Subtype.val hmn
    exact Subtype.ext h1
  -- the support of `f` is contained in the range of the inclusion, because
  -- `f` vanishes at the unique point `1`
  have hsupp : Function.support f ⊆ Set.range g := by
    intro x hx
    rw [Function.mem_support] at hx
    have hx1 : 1 ≤ x.1 := Set.mem_Ici.mp x.2
    rcases lt_or_eq_of_le hx1 with h | h
    · -- `x` is at least `2`, so it is in the image of `g`
      refine ⟨⟨x.1, h⟩, ?_⟩
      exact Subtype.ext rfl
    · -- `x = 1`, where `f` vanishes by hypothesis
      exfalso
      have hxeq : x = ⟨1, by simp⟩ := Subtype.ext h.symm
      exact hx (by rw [hxeq]; exact h0)
  exact (Function.Injective.tsum_eq hinj hsupp).symm

end Work.FunctionalEquations
