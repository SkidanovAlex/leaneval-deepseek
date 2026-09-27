import Mathlib

/-!
# Definitions for the "spines to infinity" construction

The construction of pairwise disjoint, locally finite, closed, preconnected, non-compact
"spines" `A b ∋ b` through a locally finite set `B` in a connected non-compact `n`-manifold
(`n ≥ 2`) uses a compact exhaustion `K` with `K i ⊆ interior (K (i+1))`.

The basic layers of `M` are the **shells**

`Shell K i = interior (K (i+1)) \ K i`,

which are open and pairwise disjoint (but do not cover `M`: the "walls" `K i \ interior (K i)`
are missed).
-/

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- The `K`-shell of level `i`: `interior (K (i+1)) \ K i`. -/
def Shell (K : ℕ → Set M) (i : ℕ) : Set M := interior (K (i+1)) \ K i

/-- `K` is monotone for a nested exhaustion. -/
lemma monotone_K (K : ℕ → Set M) (hKsub : ∀ i, K i ⊆ interior (K (i+1))) :
    Monotone K := by
  intro i j hij
  induction hij with
  | refl => exact subset_rfl
  | @step j _ ih => exact ih.trans ((hKsub j).trans interior_subset)

lemma isOpen_shell (K : ℕ → Set M) {i : ℕ} (h : IsClosed (K i)) : IsOpen (Shell K i) :=
  isOpen_interior.sdiff h

lemma shell_disjoint (K : ℕ → Set M) (hKsub : ∀ i, K i ⊆ interior (K (i+1)))
    {i j : ℕ} (h : i ≠ j) : Disjoint (Shell K i) (Shell K j) := by
  rcases lt_or_gt_of_ne h with h | h
  · refine Set.disjoint_left.mpr fun x hx hy => ?_
    exact hy.2 (monotone_K K hKsub (Nat.succ_le_of_lt h) (interior_subset hx.1))
  · refine Set.disjoint_left.mpr fun x hx hy => ?_
    exact hx.2 (monotone_K K hKsub (Nat.succ_le_of_lt h) (interior_subset hy.1))

end Work.Noncompact.CompressionTube

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- The data produced by the recursive routing of the spines: a level `lev b` for every `b ∈ B`
(the largest level not yet occupied by `b`), junction points `q b i` in the shells, and arcs
`γ b i` from `q b i` to `q b (i+1)`, subject to the invariants that make the assembly work.

The arcs at a fixed level are pairwise disjoint for different strands, and the *footprint*
`γ b i '' Icc 0 1 ∩ (interior (K (i+2)) \ K (i+1))` of a level-`i` arc in the next shell is
disjoint from every level-`(i+1)` arc of a different strand.  These two conditions are exactly
what is needed to prove the pairwise disjointness of the assembled spines. -/
structure SpineData (K : ℕ → Set M) (B : Set M) (lev : B → ℕ) (q : B → ℕ → M)
    (γ : B → ℕ → ℝ → M) : Prop where
  lev_notMem : ∀ b, (b : M) ∉ K (lev b)
  lev_mem_succ : ∀ b, (b : M) ∈ K (lev b + 1)
  q_shell : ∀ b i, lev b < i → q b i ∈ interior (K (i+1)) \ K i
  q_lev : ∀ b, q b (lev b) = (b : M)
  cont : ∀ b i, lev b ≤ i → Continuous (γ b i)
  inj : ∀ b i, lev b ≤ i → Set.InjOn (γ b i) (Set.Icc (0:ℝ) 1)
  ends : ∀ b i, lev b ≤ i → γ b i 0 = q b i ∧ γ b i 1 = q b (i+1)
  image_sub : ∀ b i, lev b ≤ i → ∀ t ∈ Set.Icc (0:ℝ) 1, γ b i t ∈ interior (K (i+2))
  disjoint_K : ∀ b i, lev b ≤ i → Disjoint (γ b i '' Set.Icc (0:ℝ) 1) (K i)
  disjoint_same : ∀ b b' i, lev b ≤ i → lev b' ≤ i → b ≠ b' →
      Disjoint (γ b i '' Set.Icc (0:ℝ) 1) (γ b' i '' Set.Icc (0:ℝ) 1)
  disjoint_foot : ∀ b b' i, lev b ≤ i → lev b' ≤ i + 1 → b ≠ b' →
      Disjoint ((γ b i '' Set.Icc (0:ℝ) 1) ∩ (interior (K (i+2)) \ K (i+1)))
        (γ b' (i+1) '' Set.Icc (0:ℝ) 1)
  avoids_base : ∀ b b' i, lev b ≤ i → b ≠ b' → (b' : M) ∉ γ b i '' Set.Icc (0:ℝ) 1

end Work.Noncompact.CompressionTube
