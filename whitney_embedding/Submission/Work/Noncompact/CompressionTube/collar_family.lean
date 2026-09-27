import Mathlib
import Submission.Work.Noncompact.CompressionTube.exists_collar_pocketFree_open
import Submission.Work.Noncompact.CompressionTube.shell_nonempty

/-!
# The collar family of the spine recursion

One **gate collar** `L j` per level, with its collar set `U j`, for the exhaustion `K` of the spine
recursion.  `L j` is a closed pocket-free collar of `K (j+1)` inside `interior (K (j+2))`, and
`U j` is an open set, disjoint from `L j`, avoiding `L j` and carrying the chart-ball pieces at
`frontier (L j)`; moreover `L j` avoids the base points that become active at level `j+1`.

The collars are produced level by level from
`Work.Noncompact.CompressionTube.exists_collar_pocketFree_open`; the degenerate case
`K (j+1) = ∅` (in which there is no point of `interior (K (j+2)) \ K (j+1)` to anchor the
construction, but also no strand to route) is handled by `L j = U j = ∅`.
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {M : Type*} [TopologicalSpace M]

/-- **The frontier of a collar lies in the shell.**  For closed `L` with `A ⊆ interior L`,
`L ⊆ interior B` and `A ⊆ interior B`, the frontier of `L` lies in the shell
`interior B \ A`. -/
theorem frontier_collar_subset_shell {A B L : Set M} (hLc : IsClosed L)
    (hAL : A ⊆ interior L) (hLB : L ⊆ interior B) :
    frontier L ⊆ interior B \ A := by
  intro z hz
  refine ⟨hLB (hLc.closure_eq ▸ frontier_subset_closure hz), fun hzA => ?_⟩
  have hzint : z ∈ interior L := hAL hzA
  rw [hLc.frontier_eq] at hz
  exact hz.2 hzint

end Work.Noncompact.CompressionTube

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **The collar family.** -/
theorem exists_collar_family {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    {K : ℕ → Set M} (hKc : ∀ i, IsCompact (K i))
    (hKsub : ∀ i, K i ⊆ interior (K (i+1)))
    (hKpf : ∀ i (x : M), x ∉ K i → ¬ IsCompact (closure (connectedComponentIn ((K i)ᶜ) x)))
    (hM : ¬ CompactSpace M) {B : Set M}
    (hB : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite) :
    ∃ (L U : ℕ → Set M),
      (∀ j, IsClosed (L j)) ∧ (∀ j, K (j+1) ⊆ interior (L j)) ∧
      (∀ j, L j ⊆ interior (K (j+2))) ∧
      (∀ j (x : M), x ∉ L j → ¬ IsCompact (closure (connectedComponentIn ((L j)ᶜ) x))) ∧
      (∀ j, IsOpen (U j)) ∧ (∀ j, Disjoint (U j) (L j)) ∧
      (∀ j, Disjoint (L j) (B ∩ (K (j+2) \ K (j+1)))) ∧
      (∀ j z, z ∈ frontier (L j) →
        ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
          z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ U j) := by
  classical
  have hkey : ∀ j, ∃ (L U : Set M),
      IsClosed L ∧ K (j+1) ⊆ interior L ∧ L ⊆ interior (K (j+2)) ∧
      (∀ x : M, x ∉ L → ¬ IsCompact (closure (connectedComponentIn (Lᶜ) x))) ∧
      IsOpen U ∧ Disjoint U L ∧ Disjoint L (B ∩ (K (j+2) \ K (j+1))) ∧
      (∀ z ∈ frontier L, ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
        z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ U) := by
    intro j
    by_cases hj : (K (j+1)).Nonempty
    · obtain ⟨w, hw⟩ := exists_shell_nonempty hM hKc hKsub (j+1) hj
      have hSA : Disjoint (B ∩ (K (j+2) \ K (j+1))) (K (j+1)) := by
        rw [Set.disjoint_left]
        intro s hs hsK
        exact hs.2.2 hsK
      have hSfin : (B ∩ (K (j+2) \ K (j+1))).Finite :=
        (hB (K (j+2)) (hKc (j+2))).subset (by intro x hx; exact ⟨hx.1, hx.2.1⟩)
      obtain ⟨L, U, hLc, hAL, hLB, hLS, hpf, hUo, _hwU, _hSU, _hUA, hUL, hpiece⟩ :=
        exists_collar_pocketFree_open (n := n) (A := K (j+1)) (B := K (j+2))
          (S := B ∩ (K (j+2) \ K (j+1))) (hKc (j+1))
          (hKc (j+2)).isClosed (hKc (j+2)) (hKsub (j+1)) (hKpf (j+1)) (hKpf (j+2))
          hSfin hSA hw
      exact ⟨L, U, hLc, hAL, hLB, hpf, hUo, hUL, hLS, hpiece⟩
    · have hK1 : K (j+1) = ∅ := Set.not_nonempty_iff_eq_empty.mp hj
      refine ⟨∅, ∅, isClosed_empty, ?_, ?_, ?_, isOpen_empty, ?_, ?_, ?_⟩
      · rw [hK1]; exact Set.empty_subset _
      · exact Set.empty_subset _
      · intro x _
        have hcomp : connectedComponentIn ((∅ : Set M)ᶜ) x = Set.univ := by
          rw [Set.compl_empty]
          exact le_antisymm (Set.subset_univ _)
            (isPreconnected_univ.subset_connectedComponentIn (Set.mem_univ x) subset_rfl)
        rw [hcomp, closure_univ]
        intro hcon
        exact hM (isCompact_univ_iff.mp hcon)
      · exact disjoint_bot_left
      · exact disjoint_bot_left
      · intro z hz
        rw [frontier_empty] at hz
        exact absurd hz (Set.notMem_empty z)
  choose L U hL using hkey
  exact ⟨L, U, fun j => (hL j).1, fun j => (hL j).2.1, fun j => (hL j).2.2.1,
    fun j => (hL j).2.2.2.1, fun j => (hL j).2.2.2.2.1, fun j => (hL j).2.2.2.2.2.1,
    fun j => (hL j).2.2.2.2.2.2.1, fun j => (hL j).2.2.2.2.2.2.2⟩

end Work.Noncompact.CompressionTube
