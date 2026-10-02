import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.OneFact.N5.StepTools
import Submission.Work.Deep.GKO.OneFact.N5.card_filter_nmate_mem_le
import Submission.Work.Deep.GKO.OneFact.N5.exists_pairClosedSubset_card

/-!
# `exists_dumpSet`: the balancing step of the N5b completion

This module proves `Work.Deep.GKO.OneFact.N5.exists_dumpSet`, the "balance" step of the proof of
N5b (`completeInsideMatching`): if an inside matching `N` leaves `|U ∩ A| - |U ∩ B|` more vertices
uncovered on the `A`-side than on the `B`-side (`U = uncov N`), then one can delete `d` of the
`N`-edges lying inside `B`, avoiding a forbidden set `F`, and thereby lower `|U ∩ B|` by `2d`.

The output is the vertex set `D` of the deleted edges: a union of `N`-edges, contained in `B`,
disjoint from `F` and from `U`, of cardinality `2d`.

## The proof

Write `U = uncov N` and let `mate := nmate N` be the mate map of the matching `N` (the unique
`N`-neighbour of a covered vertex).  The candidate set is

`R = {x ∈ B : x ∉ U, x ∉ F, mate x ∉ F}`,

which is closed under `mate` (a covered vertex of `B` has its mate in `B`, by the hypothesis that
`N`'s edges are inside `A` or inside `B`).  Two observations:

* `B \ R ⊆ (U ∩ B) ∪ (F ∩ B) ∪ {x ∈ B : mate x ∈ F}`, and the last set has at most `F.card`
  elements because `mate` is injective (`nmate` is an involution with no fixed point on covered
  vertices).  Since `R ⊆ B`, this gives
  `R.card ≥ B.card - (|U ∩ B| + 2 |F|) ≥ |U ∩ A| - |U ∩ B| = 2d`, using the room hypothesis
  `|U ∩ A| + 2 |F| ≤ B.card`.
* `R` is a disjoint union of `mate`-pairs, so it contains a `mate`-closed subset `D` of any even
  cardinality `2d ≤ R.card` (`exists_pairClosedSubset_card`).

Any such `D` is a union of `d` edges of `N` inside `B` avoiding `F` and `U`, which is exactly the
conclusion.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

namespace Work.Deep.GKO.OneFact.N5

noncomputable section

variable {n : ℕ}

/-- The `N`-mate of a covered vertex of `B` lies in `B`, provided the edges of `N` are inside `A`
or inside `B`. -/
theorem nmate_mem_of_mem_B {A B : Finset (Fin n)} (hAB : Disjoint A B)
    {N : SimpleGraph (Fin n)}
    (hNin : ∀ u v, N.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    {x : Fin n} (hx : x ∈ B) (hxu : x ∉ uncov N) : nmate N x ∈ B := by
  have hcov : ∃ w, N.Adj x w := (not_mem_uncov_iff N x).mp hxu
  have hadj : N.Adj x (nmate N x) := nmate_spec hcov
  rcases hNin x (nmate N x) hadj with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd hx (Finset.disjoint_left.mp hAB h1)
  · exact h2

theorem exists_dumpSet {n : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hcov : A ∪ B = Finset.univ) (N : SimpleGraph (Fin n))
    (hN : Work.Deep.GKO.IsMatching' N)
    (hNin : ∀ u v, N.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (F : Finset (Fin n)) {d : ℕ}
    (hd : 2 * d = (Work.Deep.GKO.OneFact.N5.uncov N ∩ A).card
      - (Work.Deep.GKO.OneFact.N5.uncov N ∩ B).card)
    (hroom : (Work.Deep.GKO.OneFact.N5.uncov N ∩ A).card + 2 * F.card ≤ B.card) :
    ∃ D : Finset (Fin n), D ⊆ B ∧ D.card = 2 * d ∧ Disjoint D F ∧
      Disjoint D (Work.Deep.GKO.OneFact.N5.uncov N) ∧
      (∀ x ∈ D, ∃ y ∈ D, N.Adj x y) ∧
      (∀ x ∈ D, ∀ y, N.Adj x y → y ∈ D) := by
  classical
  by_cases hle : (uncov N ∩ A).card ≤ (uncov N ∩ B).card
  · -- nothing to dump: the difference of the two uncovered numbers is `0`, hence `d = 0`
    have hdz : d = 0 := by
      have h2 : 2 * d = 0 := by rw [hd, Nat.sub_eq_zero_of_le hle]
      omega
    exact ⟨∅, by simp [hdz]⟩
  · have hlt : (uncov N ∩ B).card < (uncov N ∩ A).card := not_le.mp hle
    -- the candidate vertex set: covered `B`-vertices whose mate avoids `F`
    set R : Finset (Fin n) := B.filter (fun x => x ∉ uncov N ∧ x ∉ F ∧ nmate N x ∉ F) with hRdef
    have hRmem : ∀ x : Fin n, x ∈ R ↔ x ∈ B ∧ x ∉ uncov N ∧ x ∉ F ∧ nmate N x ∉ F := by
      intro x
      rw [hRdef]
      exact Finset.mem_filter
    have hRsub : R ⊆ B := fun x hx => ((hRmem x).mp hx).1
    have hRclosed : ∀ x ∈ R, nmate N x ∈ R := by
      intro x hx
      obtain ⟨hxB, hxU, hxF, hmxF⟩ := (hRmem x).mp hx
      have hcov : ∃ w, N.Adj x w := (not_mem_uncov_iff N x).mp hxU
      have hadj : N.Adj x (nmate N x) := nmate_spec hcov
      refine (hRmem (nmate N x)).mpr ⟨?_, ?_, hmxF, ?_⟩
      · exact nmate_mem_of_mem_B hAB hNin hxB hxU
      · exact (not_mem_uncov_iff N (nmate N x)).mpr ⟨x, (N.adj_comm x (nmate N x)).mp hadj⟩
      · rw [nmate_invol hN hcov]
        exact hxF
    -- what leaves `R`
    have hBR : B \ R ⊆ (uncov N ∩ B) ∪ (F ∩ B) ∪ (B.filter fun x => nmate N x ∈ F) := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxB, hxR⟩ := hx
      have hout : x ∈ uncov N ∨ x ∈ F ∨ nmate N x ∈ F := by
        by_contra hc
        simp only [not_or] at hc
        exact hxR ((hRmem x).mpr ⟨hxB, hc.1, hc.2.1, hc.2.2⟩)
      rcases hout with hU | hF | hM
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hU, hxB⟩))))
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hF, hxB⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hxB, hM⟩))
    have hBcard : (B \ R).card ≤ (uncov N ∩ B).card + 2 * F.card := by
      have h1 : (B \ R).card
          ≤ ((uncov N ∩ B) ∪ ((F ∩ B) ∪ (B.filter fun x => nmate N x ∈ F))).card :=
        Finset.card_le_card (by rw [← Finset.union_assoc]; exact hBR)
      have h2 := Finset.card_union_le (uncov N ∩ B) ((F ∩ B) ∪ (B.filter fun x => nmate N x ∈ F))
      have h3 := Finset.card_union_le (F ∩ B) (B.filter fun x => nmate N x ∈ F)
      have h4 : (F ∩ B).card ≤ F.card := Finset.card_le_card Finset.inter_subset_left
      have h5 : (B.filter fun x => nmate N x ∈ F).card ≤ F.card := by
        refine le_trans (Finset.card_le_card ?_) (card_filter_nmate_mem_le hN F)
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2⟩
      omega
    have hsdiff : (B \ R).card = B.card - R.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRsub]
    have h2d : 2 * d ≤ R.card := by
      have hRB : R.card ≤ B.card := Finset.card_le_card hRsub
      omega
    -- extract a `mate`-closed subset of `R` of cardinality exactly `2d`
    obtain ⟨D, hDsub, hDcard, hDclosed⟩ :=
      exists_pairClosedSubset_card R (nmate N) d hRclosed
        (fun x hx => nmate_invol hN ((not_mem_uncov_iff N x).mp ((hRmem x).mp hx).2.1))
        (fun x hx h => by
          have hadj : N.Adj x (nmate N x) :=
            nmate_spec ((not_mem_uncov_iff N x).mp ((hRmem x).mp hx).2.1)
          rw [h] at hadj
          exact N.loopless.1 x hadj) h2d
    refine ⟨D, fun x hx => hRsub (hDsub hx), hDcard, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hxF
      exact ((hRmem x).mp (hDsub hx)).2.2.1 hxF
    · rw [Finset.disjoint_left]
      intro x hx hxU
      exact ((hRmem x).mp (hDsub hx)).2.1 hxU
    · intro x hx
      exact ⟨nmate N x, hDclosed x hx,
        nmate_spec ((not_mem_uncov_iff N x).mp ((hRmem x).mp (hDsub hx)).2.1)⟩
    · intro x hx y hxy
      rw [← nmate_eq_of hN hxy]
      exact hDclosed x hx

end

end Work.Deep.GKO.OneFact.N5
