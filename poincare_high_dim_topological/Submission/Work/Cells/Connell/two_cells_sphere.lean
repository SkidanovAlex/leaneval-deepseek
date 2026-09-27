import Mathlib
import Submission.Work.Cells.Connell.Defs
import Submission.Work.Cells.Connell.Basic
import Submission.Work.Cells.Connell.exists_notMem_of_isOpenCell_compactSpace
import Submission.Work.Cells.Connell.exists_openCell_of_compact_subset_compl_point

open Set Metric

namespace Work.Cells.Connell

/- **Connell's two-cell step (blueprint `C4`)**: a compact metric space that is a union of
two open `n`-cells (`n ≥ 1`) has a point `q` whose complement is homeomorphic to `ℝⁿ`.

Such a space is a compact manifold-like object; the point `q` is the one "at infinity".
Concretely, `q` is any point missed by one of the two cells (which exists because a compact
space cannot be a single open `n`-cell), and then every compact subset of `M ∖ {q}` can be
enlarged to another open `n`-cell missing `q` (radial expansion of `ℝⁿ` plus extension of
compactly supported homeomorphisms).  Brown's criterion for `M ∖ {q}` finishes the proof. -/
set_option linter.style.haveILetI false in
theorem two_cells_sphere {n : ℕ} (hn : 1 ≤ n) {M : Type*} [MetricSpace M] [CompactSpace M]
    (h : PL.CellCover n M 2) (hbrown : BrownCriterionAt n M) (hrad : RadialExpandForm n)
    (hext : ExtHomeoForm n) :
    ∃ q : M, Nonempty (↥({q}ᶜ : Set M) ≃ₜ PL.E n) := by
  obtain ⟨W, hW, hcov⟩ := h
  have h0 : PL.IsOpenCell n (W 0) := hW 0
  have h1 : PL.IsOpenCell n (W 1) := hW 1
  -- a point missed by the first cell
  obtain ⟨q, hq⟩ := exists_notMem_of_isOpenCell_compactSpace hn h0
  refine ⟨q, ?_⟩
  -- the two cells cover `M`
  have hunion : W 0 ∪ W 1 = univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, W i := by rw [hcov]; exact Set.mem_univ x
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  -- `M ∖ {q}` is a locally compact, second countable space
  haveI : LocallyCompactSpace ↥({q}ᶜ : Set M) :=
    (isClosed_singleton.isOpen_compl).locallyCompactSpace
  -- Brown's criterion at `M ∖ {q}`
  refine hbrown ↥({q}ᶜ : Set M) ?_
  intro K hK
  -- the corresponding compact subset of `M` misses `q`
  have hK' : IsCompact (Subtype.val '' K : Set M) := hK.image continuous_subtype_val
  have hqK' : q ∉ (Subtype.val '' K : Set M) := by
    rintro ⟨x, -, hx⟩
    have hx' : (x : M) ∈ ({q}ᶜ : Set M) := x.2
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx'
    exact hx' hx
  -- enlarge `K` to an open `n`-cell of `M` missing `q`
  obtain ⟨U, hUcell, hKU, hqU⟩ :=
    exists_openCell_of_compact_subset_compl_point hn h0 h1 hunion q hq hrad hext
      (Subtype.val '' K) hK' hqK'
  -- transport this cell to the subtype `M ∖ {q}`
  refine ⟨{x : ↥({q}ᶜ : Set M) | (x : M) ∈ U}, ?_, ?_, ?_⟩
  · exact hUcell.1.preimage continuous_subtype_val
  · rintro x hx
    exact hKU ⟨x, hx, rfl⟩
  · exact isOpenCell_subtype hUcell (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h => hqU (h ▸ hx))

end Work.Cells.Connell
