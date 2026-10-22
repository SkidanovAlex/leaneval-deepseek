/-
A compact subset of a CW complex is contained in a finite skeleton.

The argument (the standard one, via the weak topology of a CW complex):

* if `K ⊆ C` were contained in no skeleton `skel C n`, then for each `k` we could pick a point
  `x k ∈ K` whose supporting cell has dimension `> k` (`exists_seq_dim_growth`);
* every subset of `S = range x` meets each closed cell in a finite set, because a point supported
  in dimension `n` lies in the `d`-skeleton only when `n ≤ d`, and the index of a point of `S` is
  bounded by its supporting dimension (`finite_inter_closedCell_of_range`); hence every subset of
  `S` is closed in `C` (`isClosed_of_finite_inter_closedCell`);
* the decreasing sequence of closed sets `Z k = {x m : m ≥ k}` has empty intersection (a point of
  `C` lies in some skeleton, so it can occur only finitely often in `x`), so compactness of `K`
  produces a finite subfamily with empty intersection — contradiction.
-/
import Mathlib
import Submission.Work.CWTOP.CellDim
import Submission.Work.CWTOP.isClosed_of_finite_inter_closedCell
import Submission.Work.CWTOP.finite_inter_closedCell_of_range
import Submission.Work.CWTOP.exists_seq_dim_growth

namespace Work.CWTOP

open Set Topology

theorem exists_skel_superset_of_isCompact {X : Type} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C] {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ n : ℕ, K ⊆ Work.CWTOP.skel C n := by
  by_contra h
  push_neg at h
  -- choose points of `K` of arbitrarily large cell dimension
  obtain ⟨x, hxK, hxdim⟩ := exists_seq_dim_growth hKC h
  -- the tails of this sequence
  let Z : ℕ → Set X := fun k => Set.range (fun m => x (k + m))
  -- every tail is closed, being a set meeting each closed cell in finitely many points
  have hZclosed : ∀ k, IsClosed (Z k) := by
    intro k
    refine isClosed_of_finite_inter_closedCell (C := C) (S := Z k) ?_ ?_
    · rintro y ⟨m, rfl⟩
      exact hKC (hxK (k + m))
    · intro d i
      exact finite_inter_closedCell_of_range (C := C) hxdim (T := Z k)
        (by rintro y ⟨m, rfl⟩; exact ⟨k + m, rfl⟩) d i
  -- the tails have empty intersection
  have hempty : Disjoint K (⋂ k, Z k) := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyK, hy⟩
    rw [mem_iInter] at hy
    -- `y` lies in some open cell, hence in some skeleton
    obtain ⟨n₀, j₀, hycell⟩ := exists_openCell_of_mem (C := C) (hKC hyK)
    have hyskel : y ∈ skel C n₀ :=
      RelCWComplex.openCell_subset_skeleton (C := C) n₀ j₀ hycell
    -- but `y` occurs in arbitrarily late tails of the sequence
    obtain ⟨s, hs⟩ := hy n₀
    obtain ⟨n, j, hkn, hmem⟩ := hxdim (n₀ + s)
    have hs' : x (n₀ + s) = y := hs
    have hyskel' : x (n₀ + s) ∈ skel C n₀ := by rw [hs']; exact hyskel
    have hle : n ≤ n₀ := le_of_mem_openCell_of_mem_skel hmem hyskel'
    exact absurd (lt_of_lt_of_le hkn hle) (not_lt.mpr (Nat.le_add_right n₀ s))
  -- compactness: finitely many of the tails already miss `K`
  obtain ⟨t, ht⟩ := hK.elim_finite_subfamily_closed Z hZclosed hempty
  -- but the point `x (max t + 1)` lies in all of them
  have hmem : x (t.sup id + 1) ∈ K ∩ ⋂ k ∈ t, Z k := by
    refine ⟨hxK _, ?_⟩
    rw [mem_iInter₂]
    intro k hk
    have hk' : k ≤ t.sup id := Finset.le_sup (f := id) hk
    exact ⟨t.sup id + 1 - k,
      congrArg x (Nat.add_sub_cancel' (Nat.le_succ_of_le hk'))⟩
  exact (Set.disjoint_left.mp ht hmem.1) hmem.2

end Work.CWTOP
