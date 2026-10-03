-- **Namespaced copy** (`Work.OROneRel.NC`) of a colleague's module, made so that the
-- window-data pipeline can be imported *together with* the Freiheitssatz pipeline:
-- `Work.OROneRel.decor_replicate_true` (declared in `Submission.Work.OROneRel.decor_wordOf_zpow_of`)
-- clashes with the declaration of the same name in
-- `Submission.Work.OROneRel.twoLetter_cycle_decor`, so no module can import both
-- `exists_window_support_data_cycred` and `bandFreiheitssatz_of_windowData`.  The copy lives in
-- the namespace `Work.OROneRel.NC`, where `decor_replicate_true` is `Work.OROneRel.NC.decor_replicate_true`
-- and no longer clashes.  Nothing here is new mathematics.
/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The window support data with a cyclically reduced root

This file proves `Work.OROneRel.NC.exists_window_support_data_cycred`: the window data of the `ℤ`-cover of
`⟨α | u ^ l⟩` (a killing weight `c`, a tight window `[lo,hi]` containing the level `1`, a tree-path
gauge `Wt`) in which the deleted walk word `winRoot Wt c lo hi u` is cyclically reduced.

## The proof

1. The data *without* the cyclic reducedness is `Work.OROneRel.NC.exists_winData_containing_one`, which
   delivers `(c, lo, hi, Wt)` with the killing property, `lo ≤ 1 ≤ hi`, the window containment, the
   tightness, the tree property, the covering and a traversed tree edge.  Its gauge is opaque, so the
   cyclic reducedness is deduced from its *stated* properties only.

2. `Work.OROneRel.forestUniq_winTree` gives `ForestUniq c (winTree Wt c lo hi)` for any gauge with
   `cohom c (Wt i) = ofAdd i` on the window (the walk of a word all of whose traversals have trivial
   loop class telescopes, so two such walks have the same group element; `NoBT` makes them reduced).

3. `Work.OROneRel.delWord_isCyclicallyReduced` gives that the *deleted word*
   `delWord (winTree Wt c lo hi) c (wordOf u)` -- the traversals of the walk of `u` whose edge is not
   in the tree -- is cyclically reduced, from `wordOf u` being reduced and cyclically reduced with
   `lsig c (wordOf u) = 0` (which is `cohom c u = 1`).

4. Finally, `winRoot Wt c lo hi u` is `FreeGroup.mk` of the list `winRootList Wt c lo hi u`, whose
   entries are exactly the deleted traversals with the edge packaged as an element of `winBeta`; a
   relabelling of the alphabet does not affect cyclic reducedness, and cyclic reducedness descends
   along it (`isCyclicallyReduced_of_map_letters` below).
-/
import Mathlib
import Submission.Work.OROneRel.exists_winData_containing_one_nc
import Submission.Work.OROneRel.exists_winWindowData_nc
import Submission.Work.OROneRel.delWordDefs
import Submission.Work.OROneRel.delWord_isCyclicallyReduced
import Submission.Work.OROneRel.forestUniq_winTree
import Submission.Work.OROneRel.isCyclicallyReducedRelator_mk

namespace Work.OROneRel.NC

universe u

variable {α : Type u}

/-! ## Relabelling the alphabet -/

/-- **Reducedness descends along a relabelling of the alphabet** (no injectivity is needed: a pair of
inverse letters is mapped to a pair of inverse letters). -/
theorem isReduced_of_map_letters {β : Type*} (f : α → β) {L : List (α × Bool)}
    (h : FreeGroup.IsReduced (L.map (fun p => (f p.1, p.2)))) : FreeGroup.IsReduced L := by
  induction L with
  | nil => exact FreeGroup.IsReduced.nil
  | cons x t ih =>
    cases t with
    | nil => exact FreeGroup.IsReduced.singleton
    | cons y t =>
      have h' : FreeGroup.IsReduced
          ((f x.1, x.2) :: (f y.1, y.2) :: t.map (fun p => (f p.1, p.2))) := by
        simpa using h
      obtain ⟨hxy, htail⟩ := FreeGroup.isReduced_cons_cons.mp h'
      refine FreeGroup.isReduced_cons_cons.mpr ⟨?_, ih htail⟩
      intro hcon
      exact hxy (by rw [hcon])

/-- **Cyclic reducedness descends along a relabelling of the alphabet.** -/
theorem isCyclicallyReduced_of_map_letters {β : Type*} (f : α → β) {L : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced (L.map (fun p => (f p.1, p.2)))) :
    FreeGroup.IsCyclicallyReduced L := by
  have h1 : FreeGroup.IsReduced
      ((L.map (fun p => (f p.1, p.2))) ++ (L.map (fun p => (f p.1, p.2)))) :=
    isCyclicallyReduced_iff_isReduced_append_self.mp h
  rw [← List.map_append] at h1
  exact isCyclicallyReduced_iff_isReduced_append_self.mpr (isReduced_of_map_letters f h1)

/-! ## The candidate root is the deleted word of the walk -/

/-- **The list of the deleted traversals.**  The candidate root is the `mk` of `winRootList`, whose
entries are the traversals of the walk of `u` whose edge is not in the tree `winTree`, with the edge
packaged as an element of `winBeta`.  Removing the packaging, one gets exactly `delWord`. -/
theorem winRootList_map_eq_delWord {α : Type u} [Fintype α] [DecidableEq α]
    (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (hwin : ∀ p ∈ decor c 0 (wordOf u), coverEdge p ∈ winE c lo hi) :
    (winRootList Wt c lo hi u).map
        (fun p : winBeta Wt c lo hi × Bool => (p.1.1, p.2))
      = delWord (winTree Wt c lo hi) c (wordOf u) := by
  classical
  -- On the walk of `u` the two filter tests are complementary: `hwin` puts every traversed edge
  -- in the window, and `winTree` is by definition the set of window edges of trivial loop class.
  rw [winRootList, delWord, List.map_filterMap]
  apply List.filterMap_congr
  intro p hp
  have hW := hwin p hp
  by_cases hP : coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) ≠ 1
  · rw [dif_pos hP]
    simp only [Option.map_some, mem_winTree]
    rw [if_neg (fun hc : coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) = 1 =>
      hP.2 hc.2)]
  · rw [dif_neg hP]
    simp only [Option.map_none, mem_winTree]
    rw [if_pos ⟨hW, by by_contra hc; exact hP ⟨hW, hc⟩⟩]

/-! ## The main theorem -/

theorem exists_window_support_data_cycred {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0) :
    ∃ (c : α → ℤ) (lo hi : ℤ) (Wt : ℤ → FreeGroup α),
      Work.OROneRel.cohom c u = 1 ∧ Wt 0 = 1 ∧
      (∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i) ∧
      lo ≤ 1 ∧ 1 ≤ hi ∧
      (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
        Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) ∧
      (∀ k : ℤ, k ≠ 0 →
        ¬ (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
            lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
              p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi)) ∧
      (∀ i : ℤ, lo ≤ i → i ≤ hi →
        ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
          Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi) ∧
      (∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi) ∧
      (∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
        Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi) ∧
      Work.OROneRel.IsCyclicallyReducedRelator (Work.OROneRel.winRoot Wt c lo hi u) := by
  classical
  obtain ⟨c, lo, hi, Wt, hcu, hW0, hcoh, hlo, hhi, hwin, hone, htree, hcov, hlast⟩ :=
    exists_winData_containing_one u hu hn hbad
  refine ⟨c, lo, hi, Wt, hcu, hW0, hcoh, hlo, hhi, hwin, hone, htree, hcov, hlast, ?_⟩
  -- The remaining goal is the cyclic reducedness of the candidate root.
  -- `wordOf u` is reduced and (because `cohom c u = 1`) of weight zero, and cyclic reducedness of
  -- the relator transports to `wordOf u`; the tree `winTree Wt c lo hi` is a forest
  -- (`forestUniq_winTree`), so the deleted word is cyclically reduced
  -- (`delWord_isCyclicallyReduced`), and `winRootList_map_eq_delWord` identifies it with the
  -- image of the candidate root-word under the relabelling of the alphabet.
  have hred : FreeGroup.IsReduced (wordOf u) := by
    unfold wordOf
    exact @FreeGroup.isReduced_toWord α (Classical.decEq α) u
  have hcycw : FreeGroup.IsCyclicallyReduced (wordOf u) := by
    simpa [IsCyclicallyReducedRelator, wordOf] using hcyc
  have h0 : lsig c (wordOf u) = 0 := by
    have h := cohom_mk c (wordOf u)
    rw [mk_wordOf u, hcu] at h
    have h2 := congrArg Multiplicative.toAdd h
    simpa using h2.symm
  have hforest : ForestUniq c (winTree Wt c lo hi) :=
    forestUniq_winTree Wt c lo hi (fun i _ _ => hcoh i)
  have hdel := delWord_isCyclicallyReduced c (winTree Wt c lo hi) hred hcycw h0 hforest
  have hmap := winRootList_map_eq_delWord Wt c lo hi u hwin
  have hgoal : FreeGroup.IsCyclicallyReduced (winRootList Wt c lo hi u) :=
    isCyclicallyReduced_of_map_letters (Subtype.val : winBeta Wt c lo hi → α × ℤ)
      (hmap.symm ▸ hdel)
  rw [winRoot]
  exact isCyclicallyReducedRelator_mk hgoal

end Work.OROneRel.NC
