/-
If a subset `K` of a CW complex `C` is contained in no finite skeleton, then there is a sequence
in `K` whose `k`-th term is supported in a cell of dimension `> k`.

The proof is a direct choice: `¬ K ⊆ skel C k` gives `y ∈ K \ skel C k`; the point `y ∈ C` lies in
some open cell `openCell n j`, and `openCell n j ⊆ skel C n`, so `n > k`.
-/
import Mathlib
import Submission.Work.CWTOP.CellDim

namespace Work.CWTOP

open Set Topology

theorem exists_seq_dim_growth {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [Topology.CWComplex C] {K : Set X} (hKC : K ⊆ C) (h : ∀ n, ¬ K ⊆ Work.CWTOP.skel C n) :
    ∃ x : ℕ → X, (∀ k, x k ∈ K) ∧
      ∀ k, ∃ (n : ℕ) (j : Topology.RelCWComplex.cell C n),
        k < n ∧ x k ∈ Topology.RelCWComplex.openCell n j := by
  classical
  have hchoice : ∀ k : ℕ, ∃ y : X, y ∈ K ∧
      ∃ (n : ℕ) (j : Topology.RelCWComplex.cell C n),
        k < n ∧ y ∈ Topology.RelCWComplex.openCell n j := by
    intro k
    obtain ⟨y, hyK, hySk⟩ := Set.not_subset.mp (h k)
    obtain ⟨n, j, hycell⟩ := exists_openCell_of_mem (C := C) (hKC hyK)
    have hkn : k < n := by
      by_contra hle
      exact hySk (skel_mono (C := C) (Nat.le_of_not_lt hle)
        (RelCWComplex.openCell_subset_skeleton (C := C) n j hycell))
    exact ⟨y, hyK, n, j, hkn, hycell⟩
  choose x hx using hchoice
  exact ⟨x, fun k => (hx k).1, fun k => (hx k).2⟩

end Work.CWTOP
