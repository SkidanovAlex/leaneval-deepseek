import Mathlib

/-!
# van Kampen generation for a two-set open cover (first step)

The first honest step of the Mayer–Vietoris / van Kampen input: a path in a union of two open sets
is a concatenation of finitely many paths, each lying entirely in one of the two sets, and at every
junction where the label changes the junction point lies in the intersection.

Mathlib already contains the Lebesgue subdivision this rests on
(`exists_monotone_Icc_subset_open_cover_unitInterval`); the content here is the bookkeeping turning a
subdivision of the *unit interval* along the cover of the unit interval into a decomposition of the
*path* along the cover of the ambient space, together with the junction condition.
-/

open Set
open scoped unitInterval

namespace Commons.Topology.Homotopy

/-- **van Kampen decomposition along a two-set open cover.**

Let `A, B ⊆ X` be open and let `γ : I → X` be a path with image in `A ∪ B`.  Then there are
finitely many points `u 0 ≤ u 1 ≤ ⋯ ≤ u n` of the unit interval with `u 0 = 0`, `u n = 1`, a
labelling `c : Fin n → Bool` such that `γ` maps `[u i, u (i+1)]` into `A` (if `c i = false`) or
`B` (if `c i = true`), and at every interior junction where the two adjacent labels differ the
junction point lies in `A ∩ B`. -/
theorem exists_piecewise_decomposition_of_open_cover {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) {γ : C(Set.Icc (0 : ℝ) 1, X)}
    (hγ : ∀ t, γ t ∈ A ∪ B) :
    ∃ (n : ℕ) (_ : 0 < n) (c : Fin n → Bool) (u : Fin (n + 1) → Set.Icc (0 : ℝ) 1),
      u 0 = 0 ∧ u (Fin.last n) = 1 ∧ Monotone u ∧
      (∀ i : Fin n, ∀ s ∈ Set.Icc (u i.castSucc) (u i.succ),
        γ s ∈ (if c i = true then B else A)) ∧
      (∀ (i j : Fin n), (i : ℕ) + 1 = (j : ℕ) → c i ≠ c j →
        γ (u j.castSucc) ∈ A ∩ B) := by
  classical
  -- the two-set open cover of the unit interval pulled back along `γ`
  set c₀ : Bool → Set (Set.Icc (0 : ℝ) 1) :=
    fun b => cond b ((γ : Set.Icc (0 : ℝ) 1 → X) ⁻¹' B)
      ((γ : Set.Icc (0 : ℝ) 1 → X) ⁻¹' A) with hc₀
  have hc₀_false : c₀ false = (γ : Set.Icc (0 : ℝ) 1 → X) ⁻¹' A := by
    rw [hc₀]; rfl
  have hc₀_true : c₀ true = (γ : Set.Icc (0 : ℝ) 1 → X) ⁻¹' B := by
    rw [hc₀]; rfl
  have hc₁ : ∀ b, IsOpen (c₀ b) := by
    intro b
    rcases Bool.eq_false_or_eq_true b with hb | hb <;> rw [hb]
    · rw [hc₀_true]; exact hB.preimage γ.continuous
    · rw [hc₀_false]; exact hA.preimage γ.continuous
  have hc₂ : (univ : Set (Set.Icc (0 : ℝ) 1)) ⊆ ⋃ b, c₀ b := by
    intro s _
    have hs := hγ s
    rcases hs with h | h
    · refine mem_iUnion.mpr ⟨false, ?_⟩
      rw [hc₀_false]; exact h
    · refine mem_iUnion.mpr ⟨true, ?_⟩
      rw [hc₀_true]; exact h
  obtain ⟨t, ht0, htmono, htend, htpiece⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc₁ hc₂
  obtain ⟨m, hm⟩ := htend
  choose lab hlab using htpiece
  have hlabdef : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ c₀ (lab k) := hlab
  set u : Fin (m + 1 + 1) → Set.Icc (0 : ℝ) 1 := fun i => t i.1 with hudef
  set cc : Fin (m + 1) → Bool := fun i => lab i.1 with hcdef
  refine ⟨m + 1, Nat.succ_pos m, cc, u, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hudef]; exact ht0
  · rw [hudef]; exact hm (m + 1) (Nat.le_succ m)
  · intro i j hij
    rw [hudef]
    exact htmono (show (i : ℕ) ≤ (j : ℕ) from hij)
  · -- the piece property
    intro i s hs
    have hsub : Set.Icc (t i.1) (t (i.1 + 1)) ⊆ c₀ (lab i.1) := hlabdef i.1
    have hmem : s ∈ Set.Icc (t i.1) (t (i.1 + 1)) := by
      simpa [hudef, Fin.val_succ] using hs
    have h1 : s ∈ c₀ (lab i.1) := hsub hmem
    have h2 : γ s ∈ (if lab i.1 = true then B else A) := by
      rcases Bool.eq_false_or_eq_true (lab i.1) with hl | hl
      · rw [hl] at h1 ⊢
        rw [hc₀_true] at h1
        simp only [↓reduceIte] at h1 ⊢
        exact h1
      · rw [hl] at h1 ⊢
        rw [hc₀_false] at h1
        simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢
        exact h1
    simpa [hcdef] using h2
  · -- the junction condition
    intro i j hij hne
    have hjval : (j : ℕ) = (i : ℕ) + 1 := hij.symm
    have hpoint : u j.castSucc = t (j : ℕ) := by rw [hudef]; rfl
    have hne' : lab i.1 ≠ lab j.1 := fun h => hne h
    have hin_i : t (j : ℕ) ∈ Set.Icc (t i.1) (t (i.1 + 1)) := by
      refine ⟨htmono (show (i : ℕ) ≤ (j : ℕ) from Nat.le_of_lt (by omega)), ?_⟩
      rw [hjval]
    have hin_j : t (j : ℕ) ∈ Set.Icc (t (j : ℕ)) (t ((j : ℕ) + 1)) :=
      ⟨le_rfl, htmono (Nat.le_succ _)⟩
    have hAi : γ (t (j : ℕ)) ∈ (if lab i.1 = true then B else A) := by
      have h1 : t (j : ℕ) ∈ c₀ (lab i.1) := hlabdef i.1 hin_i
      rcases Bool.eq_false_or_eq_true (lab i.1) with hl | hl
      · rw [hl] at h1 ⊢; rw [hc₀_true] at h1
        simp only [↓reduceIte] at h1 ⊢; exact h1
      · rw [hl] at h1 ⊢; rw [hc₀_false] at h1
        simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢; exact h1
    have hAj : γ (t (j : ℕ)) ∈ (if lab j.1 = true then B else A) := by
      have h1 : t (j : ℕ) ∈ c₀ (lab j.1) := hlabdef j.1 hin_j
      rcases Bool.eq_false_or_eq_true (lab j.1) with hl | hl
      · rw [hl] at h1 ⊢; rw [hc₀_true] at h1
        simp only [↓reduceIte] at h1 ⊢; exact h1
      · rw [hl] at h1 ⊢; rw [hc₀_false] at h1
        simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢; exact h1
    rw [hpoint]
    rcases Bool.eq_false_or_eq_true (lab i.1) with hl | hl <;>
      rcases Bool.eq_false_or_eq_true (lab j.1) with hl' | hl'
    · exact absurd (by rw [hl, hl']) hne'
    · rw [hl] at hAi; rw [hl'] at hAj; exact ⟨hAj, hAi⟩
    · rw [hl] at hAi; rw [hl'] at hAj; exact ⟨hAi, hAj⟩
    · exact absurd (by rw [hl, hl']) hne'

end Commons.Topology.Homotopy
