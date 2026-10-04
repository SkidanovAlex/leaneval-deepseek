import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

/-- If `N` is `C^∞` on the open set `U`, then for every `j` the function
`p ↦ ‖iteratedFDeriv ℝ j N p‖` is continuous on `U`.

This is the "tower smoothness" fact: `iteratedFDerivWithin ℝ j N U` is continuous on `U`
whenever `N ∈ C^j` on `U` (Mathlib's `ContDiffOn.continuousOn_iteratedFDerivWithin`), and on the
open set `U` the derivative `iteratedFDerivWithin ℝ j N U` agrees with `iteratedFDeriv ℝ j N`. -/
theorem continuousOn_norm_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : E → F} {U : Set E} (hU : IsOpen U) (hN : ContDiffOn ℝ (⊤ : ℕ∞) N U) (j : ℕ) :
    ContinuousOn (fun p => ‖iteratedFDeriv ℝ j N p‖) U := by
  have hcd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) N U := hN
  have hcd' : ContDiffOn ℝ ((j : ℕ∞) : WithTop ℕ∞) N U := hcd.of_le (by exact_mod_cast le_top)
  have h1 : ContinuousOn (iteratedFDerivWithin ℝ j N U) U :=
    hcd'.continuousOn_iteratedFDerivWithin le_rfl hU.uniqueDiffOn
  have h2 : ContinuousOn (fun p => iteratedFDeriv ℝ j N p) U :=
    h1.congr (fun p hp => ((iteratedFDerivWithin_of_isOpen j hU) hp).symm)
  exact h2.norm

/-- The `j`-th iterated derivatives (`j ≤ m`) of a function that is `C^∞` on a neighbourhood of a
compact set `C` are uniformly bounded on `C`. -/
theorem compact_iteratedFDeriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : E → F) {U C : Set E} (hU : IsOpen U) (hN : ContDiffOn ℝ (⊤ : ℕ∞) N U)
    (hC : IsCompact C) (hCU : C ⊆ U) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ C, ∀ j : ℕ, j ≤ m → ‖iteratedFDeriv ℝ j N p‖ ≤ K := by
  classical
  -- Each level is bounded on the compact set `C`.
  have hbdd : ∀ j : ℕ, j ≤ m → ∃ a : ℝ, ∀ p ∈ C, ‖iteratedFDeriv ℝ j N p‖ ≤ a := by
    intro j _
    have h := hC.bddAbove_image ((continuousOn_norm_iteratedFDeriv hU hN j).mono hCU)
    rw [bddAbove_def] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, fun p hp => ha _ ⟨p, hp, rfl⟩⟩
  let b : ℕ → ℝ := fun j => if h : j ≤ m then Classical.choose (hbdd j h) else 0
  have hb : ∀ j, j ≤ m → ∀ p ∈ C, ‖iteratedFDeriv ℝ j N p‖ ≤ b j := by
    intro j hj p hp
    have hbj : b j = Classical.choose (hbdd j hj) := by
      dsimp only [b]
      rw [dite_eq_left hj]
    rw [hbj]
    exact Classical.choose_spec (hbdd j hj) p hp
  -- Combine the finitely many bounds into a single nonnegative constant.
  refine ⟨max ((Finset.range (m+1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩
    (fun j => b j)) 0, le_max_right _ _, ?_⟩
  intro p hp j hj
  exact le_trans (hb j hj p hp)
    (le_trans (Finset.le_sup' (fun j => b j) (Finset.mem_range.mpr (by omega : j < m + 1)))
      (le_max_left _ _))

end Work.Diff.STE.flat
