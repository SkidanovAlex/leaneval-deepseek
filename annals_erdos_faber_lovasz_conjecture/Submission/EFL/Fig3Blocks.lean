import Submission.EFL.ReorderingSplit
import Submission.EFL.SubfamilyConcat

/-!
# Concatenating the blocks of Figure 3

Figure 3 of the paper combines the orderings of the blocks

`𝓗₃` (the residual family, ordered by the App-3 firing) → `W₂` → `𝓗₂^good`
→ `𝓗₁^good`

into one ordering of `𝓗`.  This module supplies the combinatorial
concatenation: three blocks `A`, `B`, `C` (disjoint, covering `𝓗`), with
orderings of each and per-block bounds for the *preceding degrees* of the
concatenated ordering.  The bounds are exactly the ones the paper computes
in (b)–(d) of the proof of Theorem 6.1:

* on `A` (the first block) nothing is added;
* on `B` one adds the edges of `A` meeting the edge;
* on `C` one adds the edges of `A ∪ B` meeting the edge.

The concatenation is `exists_ordering_of_disjoint_cover` applied twice
(`SubfamilyConcat.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **Concatenation of three blocks.**  If `A`, `B`, `C` are pairwise
disjoint subfamilies covering `𝓗`, with orderings `ordA`, `ordB`, `ordC`,
and if the preceding degrees in the concatenation `A → B → C` are bounded
by `b` in the shape used by Figure 3 of the paper, then `𝓗` has an ordering
with all preceding degrees at most `b`. -/
theorem exists_ordering_of_three_blocks {𝓗 A B C : Hypergraph (Fin n)}
    (hcover : A ∪ B ∪ C = 𝓗)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {kA kB kC : ℕ} (ordA : A ≃ Fin kA) (ordB : B ≃ Fin kB) (ordC : C ≃ Fin kC)
    {b : ℝ}
    (hA : ∀ e : A, (precedingDegree A ordA e : ℝ) ≤ b)
    (hB : ∀ e : B, ((Nat.card {f : A //
          ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℝ)
        + (precedingDegree B ordB e : ℝ)) ≤ b)
    (hC : ∀ e : C, ((Nat.card {f : (A ∪ B : Hypergraph (Fin n)) //
          ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} : ℝ)
        + (precedingDegree C ordC e : ℝ)) ≤ b) :
    ∃ K : ℕ, ∃ ord : 𝓗 ≃ Fin K, ∀ e : 𝓗, (precedingDegree 𝓗 ord e : ℝ) ≤ b := by
  classical
  have hcoverAB : ((A : Hypergraph (Fin n)) ∪ B) ∪ C = 𝓗 := hcover
  -- step 1: A ⊔ B
  obtain ⟨ordAB, hABdeg⟩ := exists_ordering_of_disjoint_cover (𝓖 := (A : Hypergraph (Fin n)) ∪ B)
    (𝓖₁ := A) (𝓖₂ := B)
    rfl hAB ordA ordB (b := b) hA hB
  -- step 2: (A ∪ B) ⊔ C
  obtain ⟨ord, hdeg⟩ := exists_ordering_of_disjoint_cover (𝓖 := 𝓗) (𝓖₁ := A ∪ B) (𝓖₂ := C)
    hcoverAB (by
      rw [Set.disjoint_left]
      intro x hxAB hxC
      rcases hxAB with h | h
      · exact (Set.disjoint_left.mp hAC) h hxC
      · exact (Set.disjoint_left.mp hBC) h hxC) ordAB ordC (b := b) hABdeg hC
  exact ⟨(kA + kB) + kC, ord, hdeg⟩

end

end ErdosFaberLovaszConjecture
