import Submission.Lib.Unif2.UnifDeps

/-!
# The compact exhaustion of a Riemann surface

A second countable complex manifold is σ-compact and locally compact, hence admits a compact
exhaustion `K : ℕ → Set X` with `K n ⊆ interior (K (n+1))` and `⋃ n, K n = univ`.  The associated
increasing sequence of *open* sets `Ω n = interior (K n)` is the starting point of every exhaustion
argument in the theory of Riemann surfaces (Dirichlet problem on `Ω n`, exhaustion construction of
the Green function, ...).

This module collects the elementary topological facts about this sequence that the later modules
use.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section ExhaustionExists

variable (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]

/-- Every second countable complex manifold has a compact exhaustion. -/
theorem exists_compactExhaustion : Nonempty (CompactExhaustion X) := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  exact ⟨CompactExhaustion.choice X⟩

end ExhaustionExists

section Omega

variable {X : Type*} [TopologicalSpace X] [T2Space X] (K : CompactExhaustion X)

/-- The increasing sequence of open sets associated with a compact exhaustion. -/
def exOpen (n : ℕ) : Set X := interior (K n)

variable {K}

theorem exOpen_def (n : ℕ) : exOpen K n = interior (K n) := rfl

theorem isOpen_exOpen (n : ℕ) : IsOpen (exOpen K n) := isOpen_interior

theorem exOpen_mono : Monotone (exOpen K) := fun _ _ h => interior_mono (K.subset h)

theorem exOpen_subset_K (n : ℕ) : exOpen K n ⊆ K n := interior_subset

theorem K_subset_exOpen_succ (n : ℕ) : K n ⊆ exOpen K (n + 1) := K.subset_interior_succ n

theorem iUnion_exOpen : (⋃ n, exOpen K n) = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨n, hn⟩ := K.exists_mem x
  exact mem_iUnion.mpr ⟨n + 1, K.subset_interior_succ n hn⟩

theorem exists_mem_exOpen (x : X) : ∃ n, x ∈ exOpen K n :=
  mem_iUnion.mp (by rw [iUnion_exOpen (K := K)]; exact mem_univ x)

/-- The closure of `Ω n` is compact. -/
theorem isCompact_closure_exOpen (n : ℕ) : IsCompact (closure (exOpen K n)) :=
  IsCompact.of_isClosed_subset (K.isCompact n) isClosed_closure
    (closure_minimal (exOpen_subset_K n) (K.isCompact n).isClosed)

/-- The compact exhaustion eventually contains every compact set, in the open form. -/
theorem exists_exOpen_superset_of_isCompact {s : Set X} (hs : IsCompact s) :
    ∃ n, s ⊆ exOpen K n :=
  let ⟨n, hn⟩ := K.exists_superset_of_isCompact hs
  ⟨n + 1, hn.trans (K.subset_interior_succ n)⟩

/-- Points outside the open piece `Ω n` are not in its frontier. -/
theorem frontier_exOpen_subset_compl (n : ℕ) : frontier (exOpen K n) ⊆ (exOpen K n)ᶜ := by
  intro x hx hxs
  have : x ∈ interior (exOpen K n) := by rwa [(isOpen_exOpen n).interior_eq]
  exact (Set.disjoint_left.mp disjoint_interior_frontier this) hx

theorem exOpen_subset_interior_succ (n : ℕ) : exOpen K n ⊆ interior (K (n+1)) :=
  interior_mono (K.subset n.le_succ)

/-- A non-compact space has no exhaustion piece equal to the whole space. -/
theorem exOpen_ne_univ (hX : ¬ CompactSpace X) (n : ℕ) : exOpen K n ≠ univ := by
  intro h
  have hsub : (univ : Set X) ⊆ K n := by rw [← h]; exact exOpen_subset_K n
  exact hX (isCompact_univ_iff.mp (IsCompact.of_isClosed_subset (K.isCompact n) isClosed_univ hsub))

/-- A nonempty piece of an exhaustion of a non-compact space has nonempty frontier. -/
theorem frontier_exOpen_nonempty [PreconnectedSpace X] {n : ℕ} (hne : (exOpen K n).Nonempty)
    (hnu : exOpen K n ≠ univ) : (frontier (exOpen K n)).Nonempty := by
  by_contra hempty
  have hclopen : IsClopen (exOpen K n) :=
    isClopen_iff_frontier_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hempty)
  rcases isClopen_iff.mp hclopen with h | h
  · exact hne.ne_empty h
  · exact hnu h

end Omega

end Submission
