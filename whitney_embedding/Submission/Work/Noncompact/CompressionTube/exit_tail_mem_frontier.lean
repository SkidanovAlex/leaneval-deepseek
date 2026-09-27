import Mathlib

/-!
# The tail of an `(EXIT)` arc is on the frontier of the collar

Step 3 of the assembly (`NOTES_spine_gate_collar_SESSION.md` §18) needs: if an arc runs inside `L`
up to the split point `σ` and leaves `L` immediately after, then `α σ` lies on `frontier L`.  The
strictness `σ < 1` is essential -- for `σ = 1` the hypothesis `hout` is vacuous and the statement is
false (a constant arc inside `L`).
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **The exit point of an `(EXIT)` arc is on the frontier of the collar.** -/
theorem exit_tail_mem_frontier {M : Type*} [TopologicalSpace M] {L : Set M} (hLc : IsClosed L)
    {α : ℝ → M} (hαc : Continuous α) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hin : ∀ u ∈ Set.Icc (0:ℝ) σ, α u ∈ L)
    (hout : ∀ u ∈ Set.Ioc σ 1, α u ∉ L) :
    α σ ∈ frontier L := by
  have hL : α σ ∈ L := hin σ ⟨hσ0, le_rfl⟩
  rw [hLc.frontier_eq]
  refine ⟨hL, ?_⟩
  intro hint
  -- `interior L` is a neighbourhood of `α σ`, so `α u ∈ interior L` for `u` close to `σ`
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp
    (hαc.continuousAt (isOpen_interior.mem_nhds hint))
  -- choose `u = σ + ε` with `0 < ε < δ` and `u < 1`
  set ε : ℝ := min (δ / 2) ((1 - σ) / 2) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε1 : σ + ε < 1 := by
    have h2 : ε ≤ (1 - σ) / 2 := min_le_right _ _
    linarith
  have hmem : α (σ + ε) ∈ interior L := by
    refine hδ ?_
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hε0]
    linarith
  exact hout (σ + ε) ⟨by linarith, hε1.le⟩ (interior_subset hmem)

end Work.Noncompact.CompressionTube
