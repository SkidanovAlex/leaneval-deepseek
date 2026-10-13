import Mathlib

namespace Work.WilG4c

/-- If a non-empty set of points `S` carries a bounded set of values `|g|`, then it contains a
point whose value is within a factor `2` of the supremum (a `2`-approximate maximiser). -/
theorem exists_nearmax_of_bdd {n : ℕ} {S : Set (Fin n → ℝ)} (hS : S.Nonempty)
    (g : (Fin n → ℝ) → ℝ) (hbdd : BddAbove ((fun y => |g y|) '' S)) :
    ∃ y ∈ S, ∀ y' ∈ S, |g y'| ≤ 2 * |g y| := by
  have hne : ((fun y => |g y|) '' S).Nonempty := hS.image (fun y => |g y|)
  have hmem : ∀ y ∈ S, |g y| ≤ sSup ((fun y => |g y|) '' S) := fun y hy =>
    le_csSup hbdd ⟨y, hy, rfl⟩
  by_cases ht : sSup ((fun y => |g y|) '' S) ≤ 0
  · -- the supremum vanishes, so every value is zero
    obtain ⟨y, hy⟩ := hS
    refine ⟨y, hy, ?_⟩
    have h0 : sSup ((fun y => |g y|) '' S) = 0 :=
      le_antisymm ht (le_trans (abs_nonneg (g y)) (hmem y hy))
    have hyg : |g y| = 0 := le_antisymm (h0 ▸ hmem y hy) (abs_nonneg (g y))
    intro y' hy'
    have h1 : |g y'| ≤ 0 := h0 ▸ hmem y' hy'
    rw [hyg]
    linarith
  · -- positive supremum: pick a point strictly above half of it
    have hlt : sSup ((fun y => |g y|) '' S) / 2 < sSup ((fun y => |g y|) '' S) := by
      linarith
    obtain ⟨b, hbT, hb⟩ := (lt_csSup_iff hbdd hne).mp hlt
    obtain ⟨y, hy, hyb⟩ := hbT
    refine ⟨y, hy, ?_⟩
    rw [← hyb] at hb
    intro y' hy'
    have h1 : |g y'| ≤ sSup ((fun y => |g y|) '' S) := hmem y' hy'
    linarith

end Work.WilG4c
