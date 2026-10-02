import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.edgeCount_graphOf

/-!
# `SelfLowerRegular 𝓖 univ p ε` iff `LowerReg (graphOf 𝓖) p ε`

The hypergraph-language hypothesis `SelfLowerRegular 𝓖 Set.univ p ε` of `GKOStatement`
is exactly the graph-language `LowerReg (graphOf 𝓖) p ε`.  The two formulations differ
only in

* the (trivial, for `X = Set.univ`) side conditions `∀ a ∈ A, a ∈ X`, `∀ b ∈ B, b ∈ X`;
* the size lower bounds `ε * (Set.univ : Set (Fin n)).ncard ≤ |A|` versus
  `ε * (n : ℝ) ≤ |A|`, which agree because `(Set.univ : Set (Fin n)).ncard = n`; and
* counting with `edgeCount 𝓖 A B` versus `crossEdges (graphOf 𝓖) A B`, which agree for
  disjoint `A B` by `Work.Deep.GKO.edgeCount_graphOf`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open ErdosFaberLovaszConjecture

namespace Work.Deep.GKO

theorem selfLowerRegular_iff_lowerReg {n : ℕ} (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (p ε : ℝ) :
    ErdosFaberLovaszConjecture.SelfLowerRegular 𝓖 Set.univ p ε ↔
      Work.Deep.GKO.LowerReg (Work.Deep.GKO.graphOf 𝓖) p ε := by
  have hncard : ((Set.univ : Set (Fin n)).ncard : ℝ) = (n : ℝ) := by
    rw [Set.ncard_univ, Nat.card_fin]
  constructor
  · intro h A B hAB hA hB
    rw [Work.Deep.GKO.edgeCount_graphOf 𝓖 A B hAB]
    exact h A B (fun a _ => Set.mem_univ a) (fun b _ => Set.mem_univ b) hAB
      (by rwa [hncard]) (by rwa [hncard])
  · intro h A B _ _ hAB hA hB
    rw [← Work.Deep.GKO.edgeCount_graphOf 𝓖 A B hAB]
    exact h A B hAB (by rwa [hncard] at hA) (by rwa [hncard] at hB)

end Work.Deep.GKO
