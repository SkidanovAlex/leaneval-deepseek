import Mathlib
import Submission.Work.PL.Defs

/-!
# A compact space is never a single open `n`-cell (`n ≥ 1`)

If `M` is compact and `W ⊆ M` is an open `n`-cell (`PL.IsOpenCell n W`, i.e. `W` is open and
homeomorphic to `ℝⁿ = PL.E n`) with `n ≥ 1`, then `W` cannot be all of `M`: the complement of
`W` is nonempty.

Indeed, if `W = univ` then `M ≃ₜ PL.E n`, so `PL.E n` would be compact; but `ℝⁿ` is a
nontrivial normed `ℝ`-vector space, hence noncompact (`RealNormedSpace.noncompactSpace`).

This is the elementary topological fact behind "a compact manifold needs at least two cells":
no compact space is covered by a single open cell of positive dimension.
-/

open Set Metric

namespace Work.Cells.Connell

set_option linter.style.haveILetI false in
theorem exists_notMem_of_isOpenCell_compactSpace {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M] [CompactSpace M] {W : Set M} (hW : PL.IsOpenCell n W) :
    ∃ q : M, q ∉ W := by
  by_contra h
  -- `¬ ∃ q, q ∉ W` means every point of `M` lies in `W`, i.e. `W = univ`.
  simp only [not_exists, not_not] at h
  have hWuniv : W = univ := Set.eq_univ_iff_forall.mpr h
  obtain ⟨-, ⟨e⟩⟩ := hW
  -- `W = univ` makes `W` compact, hence `PL.E n` is compact via the homeomorphism `e`.
  have hK : IsCompact W := hWuniv.symm ▸ isCompact_univ
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hK
  haveI : CompactSpace (PL.E n) := e.compactSpace
  -- `PL.E n = ℝⁿ` is a nontrivial normed space for `n ≥ 1`, hence noncompact: contradiction.
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (inferInstance : NoncompactSpace (PL.E n)).noncompact_univ isCompact_univ

end Work.Cells.Connell
