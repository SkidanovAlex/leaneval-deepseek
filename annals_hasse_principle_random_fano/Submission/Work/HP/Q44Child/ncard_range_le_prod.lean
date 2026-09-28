import Mathlib

namespace Work.HP.Q44Child

/-- The range of a function `α → (ι → ℤ)` whose values are bounded componentwise by
`N` is finite, with cardinality at most `∏ i, (2 * N i + 1)`. -/
theorem ncard_range_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    (f : α → ι → ℤ) (N : ι → ℕ) (hN : ∀ a i, |f a i| ≤ (N i : ℤ)) :
    (Set.range f).Finite ∧ (Set.range f).ncard ≤ ∏ i, (2 * N i + 1) := by
  -- The box of all integer-valued functions with `|g i| ≤ N i`.
  let T : Finset (ι → ℤ) := Fintype.piFinset (fun i => Finset.Icc (-(N i : ℤ)) (N i : ℤ))
  have hmem : ∀ a, f a ∈ T := by
    intro a
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h := hN a i
    rw [abs_le] at h
    exact h
  have hsub : Set.range f ⊆ (T : Set (ι → ℤ)) := by
    rintro _ ⟨a, rfl⟩
    exact hmem a
  have hcard : T.card = ∏ i, (2 * N i + 1) := by
    rw [Fintype.card_piFinset]
    apply Finset.prod_congr rfl
    intro i _
    rw [Int.card_Icc]
    have h1 : (N i : ℤ) + 1 - (-(N i : ℤ)) = ((2 * N i + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [h1, Int.toNat_natCast]
  constructor
  · exact (T.finite_toSet).subset hsub
  · calc (Set.range f).ncard ≤ (T : Set (ι → ℤ)).ncard := Set.ncard_le_ncard hsub (T.finite_toSet)
      _ = T.card := Set.ncard_coe_finset T
      _ = ∏ i, (2 * N i + 1) := hcard

end Work.HP.Q44Child
