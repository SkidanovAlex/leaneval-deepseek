import Mathlib
import Submission.Work.OROneRel.exists_treeGauge
import Submission.Work.OROneRel.winBasisDefs

/-!
# The edges of the root of the exploration are tree edges

Let `c : α → ℤ` be a weight and `[lo,hi]` a window of levels.  The exploration of
`Work.OROneRel.exists_treeGauge` builds the tree-path gauge `treeGauge c lo hi` of the window by a
breadth-first search from the level `0`, which starts with the empty word at the level `0`.  The
edges of trivial loop class of the resulting gauge are the edges of the BFS tree.

This file proves `Work.OROneRel.treeGauge_edge_of_unique_witness`: if a *single* traversal of the
level `0` (a witness with `lv = 0` and `word = []`) leads to a level `x ≠ 0` -- that is, if the step
out of the root along the window edge `e` is the only way of reaching `x` from the root -- then `e`
is a tree edge of the gauge, i.e. `coverClassAt (treeGauge c lo hi) c e = 1`.

## The argument

The level `0` is the only level assigned at round `0` (`bstate_zero_eq_some_iff`), so, `x ≠ 0` being
given, the level `x` is unassigned at round `0` and the exploration reaches it exactly in the first
round, assigning it the word `Bwit.newWord q` of the witness `q = Classical.choose hbEx` that
discovered it.  Any witness that discovers `x` from the level `0` has `lv = 0` and `word = []`
(`bstate_zero_eq_some_iff`), so by the uniqueness hypothesis `q` *is* the given witness
`p₀ = ⟨0, g, b, []⟩`; hence the level `x` carries the word `Bwit.newWord p₀ = [(g,b)]` in the gauge.
The invariant `Inv` of the exploration then says that every decorated letter of the word carried by
an assigned level traverses an edge of trivial loop class, and `decor c 0 (Bwit.newWord p₀)` is
exactly `[Bwit.dec c p₀]`, whose edge is `Bwit.edge c p₀`.
-/

namespace Work.OROneRel

universe u

/-- The exploration assigns the empty word to the level `0` at round `0`. -/
theorem bstate_zero_eq_some {α : Type u} (c : α → ℤ) (lo hi : ℤ) :
    bstate c lo hi 0 0 = some ([] : List (α × Bool)) := by
  rw [bstate_zero]; simp

/-- **The only word of round `0` is the empty word at the level `0`**: a word assigned by the
exploration at round `0` carries the level `0` and is empty. -/
theorem bstate_zero_eq_some_iff {α : Type u} {c : α → ℤ} {lo hi : ℤ} {i : ℤ}
    {L : List (α × Bool)} (h : bstate c lo hi 0 i = some L) : i = 0 ∧ L = [] := by
  rw [bstate_zero] at h
  beta_reduce at h
  by_cases h0 : i = 0
  · rw [if_pos h0] at h
    exact ⟨h0, (Option.some.inj h).symm⟩
  · rw [if_neg h0] at h
    exact absurd h (by simp)

theorem treeGauge_edge_of_unique_witness {α : Type u} [Fintype α] [DecidableEq α]
    (c : α → ℤ) (lo hi : ℤ) (g : α) (b : Bool)
    (hE : Work.OROneRel.Bwit.edge c ⟨0, g, b, []⟩ ∈ Work.OROneRel.winE c lo hi)
    (hT : Work.OROneRel.Bwit.tgt c ⟨0, g, b, []⟩ ≠ 0)
    (huniq : ∀ p' : Work.OROneRel.Bwit α,
      Work.OROneRel.Bwit.edge c p' ∈ Work.OROneRel.winE c lo hi → p'.lv = 0 → p'.word = [] →
      Work.OROneRel.Bwit.tgt c p' = Work.OROneRel.Bwit.tgt c ⟨0, g, b, []⟩ →
      p' = ⟨0, g, b, []⟩) :
    Work.OROneRel.coverClassAt (Work.OROneRel.treeGauge c lo hi) c
      (Work.OROneRel.Bwit.edge c ⟨0, g, b, []⟩) = 1 := by
  classical
  -- fold the root witness and its target level
  set p₀ : Bwit α := ⟨0, g, b, []⟩ with hp₀
  -- the target level is not the root, hence it is unassigned at round `0`
  have hb0 : bstate c lo hi 0 (Bwit.tgt c p₀) = none := by
    rw [bstate_zero]; simp [hT]
  -- the given witness exhibits the target as reachable in the first round
  have hbEx : bExists c lo hi (bstate c lo hi 0) (Bwit.tgt c p₀) :=
    ⟨p₀, hE, by simp only [hp₀]; exact bstate_zero_eq_some c lo hi, rfl⟩
  -- a witness discovering the target from the root is the given one, by uniqueness
  obtain ⟨hE', hst, htg⟩ := Classical.choose_spec hbEx
  obtain ⟨hlv, hw⟩ := bstate_zero_eq_some_iff hst
  have hchoose : Classical.choose hbEx = p₀ := huniq _ hE' hlv hw htg.symm
  -- hence the target level carries the word `newWord p₀` from the first round on
  have hstep1 : bstate c lo hi 1 (Bwit.tgt c p₀) = some (Bwit.newWord p₀) := by
    have h1 : bstate c lo hi 1 (Bwit.tgt c p₀)
        = bstep c lo hi (bstate c lo hi 0) (Bwit.tgt c p₀) := bstate_succ c lo hi 0 _
    rw [h1, bstep_eq_some_of_exists hb0 hbEx, hchoose]
  have hNW : 1 ≤ NW c lo hi := by
    rw [NW]; exact Nat.le_add_left 1 _
  -- the invariant of the exploration at round `1`: every decorated letter of the word of an
  -- assigned level traverses an edge of trivial loop class
  have hInv1 := (Inv_all c lo hi 1 hNW).2 (Bwit.tgt c p₀) (Bwit.newWord p₀) hstep1
  refine hInv1.2.2.2.2 (Bwit.dec c p₀) ?_
  rw [Bwit.newWord_decor c p₀ rfl]
  exact List.mem_append_right _ (List.mem_singleton_self _)

end Work.OROneRel
