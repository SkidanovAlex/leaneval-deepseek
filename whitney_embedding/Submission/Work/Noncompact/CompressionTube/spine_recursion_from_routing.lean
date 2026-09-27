import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_state
import Submission.Work.Noncompact.CompressionTube.collar_peel
import Submission.Work.Noncompact.CompressionTube.collar_base
import Submission.Work.Noncompact.CompressionTube.collar_step

/-!
# The spine recursion (Whitney, *The self-intersections of a smooth `n`-manifold in `2n`-space*)

The construction of pairwise disjoint, locally finite, closed, preconnected, non-compact "spines"
`A b ∋ b` through a locally finite set `B` in a connected non-compact `n`-manifold (`n ≥ 2`), from
a compact exhaustion `K` with `K i ⊆ interior (K (i+1))`, `K 0 = ∅`, `⋃ K = M` and with the
*pocket freeness* hypothesis `hKpf`, as compiled by `SpineData`.

The proof is the collar ("gate") recursion:

* `exists_collar_family` (module `collar_family`) produces the collars `L j` and their sets `U j`:
  `K (j+1) ⊆ interior (L j)`, `L j ⊆ interior (K (j+2))`, `L j` pocket free, `Disjoint (U j) (L j)`,
  `L j` avoids the base points becoming active at level `j+1`, and the frontier of `L j` is crossed
  by chart balls landing in `U j` (the flatness replacing the refuted "clean exit" statements);
* `collar_peel.peel_arcs` is the single-level routing lemma: from the start points, the previous
  level's spikes and the obstacles it produces the level's `(EXIT)` arcs;
* `collar_base_LInv` (module `collar_base`) is the level-`0` datum (its "previous collar" is `∅`);
* `collar_step` (module `collar_step`) is the step from level `m` to level `m+1`;
* `spineData_of_base_step` (module `collar_state`) assembles `SpineData` from the base datum and
  the step by `Nat.rec`, and `spineData_of_seq` extracts the twelve fields of `SpineData`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Noncompact.CompressionTube

open Set Topology

theorem spine_recursion_from_routing {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] (hM : ¬ CompactSpace M) (B : Set M)
    (hB : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite)
    (K : ℕ → Set M) (hKc : ∀ i, IsCompact (K i)) (hK0 : K 0 = ∅)
    (hKsub : ∀ i, K i ⊆ interior (K (i+1))) (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (hKpf : ∀ i (x : M), x ∉ K i → ¬ IsCompact (closure (connectedComponentIn (K i)ᶜ x))) :
    ∃ (lev : B → ℕ) (q : B → ℕ → M) (γ : B → ℕ → ℝ → M),
      Work.Noncompact.CompressionTube.SpineData K B lev q γ := by
  classical
  obtain ⟨L, U, hLc, hAL, hLB, hLpf, hUo, hUL, hLavoidB, hpieces⟩ :=
    exists_collar_family (n := n) hKc hKsub hKpf hM hB
  refine spineData_of_base_step (L := L) (U := U) hK0 hKuniv ?_ ?_
  · exact collar_base_LInv (n := n) hn hB hKc hK0 hKsub hKuniv hM hLc hAL hLB hUo hUL hpieces
  · intro m st hst
    exact collar_step (n := n) hn hB hKc hK0 hKsub hKuniv hLc hAL hLB hLpf hUo hUL hLavoidB
      hpieces hst

end Work.Noncompact.CompressionTube
