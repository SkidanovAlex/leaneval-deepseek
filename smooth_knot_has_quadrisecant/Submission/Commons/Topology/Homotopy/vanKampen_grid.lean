import Mathlib

/-!
# van Kampen generation for a two-set open cover, two-dimensional (grid) form

The two-dimensional companion of `exists_piecewise_decomposition_of_open_cover`: a map from the
square into a union of two open sets can be subdivided into a grid of cells, each lying entirely in
one of the two sets.  This is the combinatorial skeleton on which the *relations* half of van Kampen
is proved (subdivide a null-homotopy, then cancel the internal edges cell by cell).

Mathlib provides the grid refinement of an open cover of the square
(`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self`); the content here is the
bookkeeping that turns it into a statement about the map `H`.
-/

open Set
open scoped unitInterval

namespace Commons.Topology.Homotopy

/-- **Grid decomposition along a two-set open cover.**

Let `A, B ⊆ X` be open and `H : I × I → X` a map with image in `A ∪ B`.  Then there is a grid
`0 = u 0 ≤ u 1 ≤ ⋯ ≤ u n = 1` of the square and a labelling `c : Fin n → Fin n → Bool` such that
every cell `[u i, u (i+1)] × [u j, u (j+1)]` is mapped by `H` into `A` (if `c i j = false`) or into
`B` (if `c i j = true`). -/
theorem exists_grid_decomposition_of_open_cover {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
    {H : C(Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, X)} (hH : ∀ p, H p ∈ A ∪ B) :
    ∃ (n : ℕ) (_ : 0 < n) (c : Fin n → Fin n → Bool) (u : Fin (n + 1) → Set.Icc (0 : ℝ) 1),
      u 0 = 0 ∧ u (Fin.last n) = 1 ∧ Monotone u ∧
      ∀ (i j : Fin n),
        ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ) ×ˢ Set.Icc (u j.castSucc) (u j.succ),
          H s ∈ (if c i j = true then B else A) := by
  classical
  set c₀ : Bool → Set (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) :=
    fun b => cond b (H ⁻¹' B) (H ⁻¹' A) with hc₀
  have hc₀_false : c₀ false = H ⁻¹' A := by rw [hc₀]; rfl
  have hc₀_true : c₀ true = H ⁻¹' B := by rw [hc₀]; rfl
  have hc₁ : ∀ b, IsOpen (c₀ b) := by
    intro b
    rcases Bool.eq_false_or_eq_true b with hb | hb <;> rw [hb]
    · rw [hc₀_true]; exact hB.preimage H.continuous
    · rw [hc₀_false]; exact hA.preimage H.continuous
  have hc₂ : (univ : Set (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1)) ⊆ ⋃ b, c₀ b := by
    intro s _
    have hs := hH s
    rcases hs with h | h
    · refine mem_iUnion.mpr ⟨false, ?_⟩
      rw [hc₀_false]; exact h
    · refine mem_iUnion.mpr ⟨true, ?_⟩
      rw [hc₀_true]; exact h
  obtain ⟨t, ht0, htmono, htend, htpiece⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hc₁ hc₂
  obtain ⟨m, hm⟩ := htend
  choose lab hlab using htpiece
  have hlabdef : ∀ k l : ℕ,
      Set.Icc (t k) (t (k + 1)) ×ˢ Set.Icc (t l) (t (l + 1)) ⊆ c₀ (lab k l) := hlab
  set u : Fin (m + 1 + 1) → Set.Icc (0 : ℝ) 1 := fun i => t i.1 with hudef
  set cc : Fin (m + 1) → Fin (m + 1) → Bool := fun i j => lab i.1 j.1 with hcdef
  refine ⟨m + 1, Nat.succ_pos m, cc, u, ?_, ?_, ?_, ?_⟩
  · rw [hudef]; exact ht0
  · rw [hudef]; exact hm (m + 1) (Nat.le_succ m)
  · intro i j hij
    rw [hudef]
    exact htmono (show (i : ℕ) ≤ (j : ℕ) from hij)
  · intro i j s hs
    have hsub : Set.Icc (t i.1) (t (i.1 + 1)) ×ˢ Set.Icc (t j.1) (t (j.1 + 1))
        ⊆ c₀ (lab i.1 j.1) := hlabdef i.1 j.1
    have hmem : s ∈ Set.Icc (t i.1) (t (i.1 + 1)) ×ˢ Set.Icc (t j.1) (t (j.1 + 1)) := by
      simpa [hudef, Fin.val_succ] using hs
    have h1 : s ∈ c₀ (lab i.1 j.1) := hsub hmem
    have h2 : H s ∈ (if lab i.1 j.1 = true then B else A) := by
      rcases Bool.eq_false_or_eq_true (lab i.1 j.1) with hl | hl
      · rw [hl] at h1 ⊢; rw [hc₀_true] at h1
        simp only [↓reduceIte] at h1 ⊢; exact h1
      · rw [hl] at h1 ⊢; rw [hc₀_false] at h1
        simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢; exact h1
    simpa [hcdef] using h2

end Commons.Topology.Homotopy
