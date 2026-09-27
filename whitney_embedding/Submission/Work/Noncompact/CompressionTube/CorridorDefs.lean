import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# Corridor chains: the routing data for the immersed line

This module isolates the geometric data through which the immersed line of the Whitney compression
is routed inside an open set `W`.  The line is built as a chain of smooth immersed pieces, one per
corridor; the corridors are pairwise "almost disjoint" (consecutive ones overlap only in a small
*neck* around the shared junction, non-consecutive ones are disjoint) and they escape every compact
set, which is what makes the resulting line proper.

The reason for isolating this as a predicate (rather than working with an arbitrary cofinal open
set) is the following.  With a bare open cofinal `W`, the one-step construction
(region `=` the component of the "just past" point of the current endpoint in
`W \ (K ∪ drawn curve)`, piece `=` germ `∪` an arc from `immersedArcWithGerm`) *does* maintain
"the current region has non-compact closure" at a **fixed** level (slit lemma
`isPreconnected_sdiff_Ico_image_arc` plus `not_isCompact_closure_sdiff`), but **increasing the level
can trap the component of the just-past point**, and properness needs unbounded levels.  With the
corridor data both problems vanish at once: the piece of stage `i` lives in `C i`, properness is the
*escape* field, and the only overlaps to control are the necks, which are around the junctions where
the pieces are joined with a common straight germ.

Both fields of this structure are provided by the spine machinery
(`Work.Noncompact.CompressionTube.SpineData`): the arcs `γ b i` of the `i`-th level satisfy
`γ b i '' Icc ⊆ interior (K (i+2)) \ K i` and join the junction points `q b i ∈ Shell K i`, so
`C i := (a small open neighbourhood of γ b i) ∩ (interior (K (i+2)) \ K i)` is open preconnected in
`W b`, contains `q b i` and `q b (i+1)`, satisfies `C i ∩ C j = ∅` for `|i-j| ≥ 2` (because
`C i ⊆ interior (K (i+2))` and `C j ⊆ M \ K j ⊆ M \ K (i+2)` for `j ≥ i+2`), and escapes every
compact set (the levels grow).  -/

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **A corridor chain through `b` inside `W`.**  Concretely: an escaping sequence of junctions
`Q i` (`Q 0 = b`) and of open preconnected corridors `C i ⊆ W` with `Q i ∈ C i`, `Q (i+1) ∈ C i`,
`C i ∩ C j = ∅` whenever `|i-j| ≥ 2`, each consecutive intersection `C i ∩ C (i+1)` confined to a
neighbourhood of `Q (i+1)` that meets no other corridor, and every `C i` for `i` large disjoint from
a prescribed compact set. -/
structure CorridorChain {M : Type*} [TopologicalSpace M] (b : M) (W : Set M) where
  /-- the junctions -/
  Q : ℕ → M
  /-- the corridors -/
  C : ℕ → Set M
  base : Q 0 = b
  isOpen_C : ∀ i, IsOpen (C i)
  isPreconnected_C : ∀ i, IsPreconnected (C i)
  subset_W : ∀ i, C i ⊆ W
  mem_Q : ∀ i, Q i ∈ C i
  mem_Q_succ : ∀ i, Q (i+1) ∈ C i
  disjoint : ∀ i j, 2 ≤ Nat.dist i j → Disjoint (C i) (C j)
  /-- the *neck* around each junction: consecutive corridors meet only inside a small open set that
  no other corridor meets -/
  neck : ∀ i, ∃ V : Set M, IsOpen V ∧ Q (i+1) ∈ V ∧ C i ∩ C (i+1) ⊆ V ∧
    (∀ k, k ≠ i → k ≠ i+1 → Disjoint V (C k))
  /-- the corridors escape every compact set -/
  escape : ∀ K : Set M, IsCompact K → ∃ I, ∀ i, I ≤ i → Disjoint (C i) K

/-- The propositional form of the corridor data (so that it can appear as a conjunct of a
`Prop`-valued statement and as a hypothesis). -/
def HasCorridorChain {M : Type*} [TopologicalSpace M] (b : M) (W : Set M) : Prop :=
  Nonempty (CorridorChain b W)

end Work.Noncompact.CompressionTube
