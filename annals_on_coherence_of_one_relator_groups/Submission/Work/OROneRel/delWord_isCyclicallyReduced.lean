/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The deleted word of a closed reduced walk with respect to a forest is cyclically reduced

Let `c : α → ℤ` be a weight, `T : Set (α × ℤ)` a set of edges of the level graph satisfying the
forest property `ForestUniq c T` (`Submission/Work/OROneRel/delWordDefs.lean`), and `w` a word which
is reduced and cyclically reduced with `lsig c w = 0`.  Then the deleted word `delWord T c w` is
cyclically reduced.

The argument is organised as follows.  Since `FreeGroup.IsCyclicallyReduced L` is equivalent to
`FreeGroup.IsReduced (L ++ L)` (`isCyclicallyReduced_iff_isReduced_append_self`), and since
`delWord` is additive over concatenations with `lsig c w = 0` (`delWordAt_append`), it suffices to
prove the *reducedness* statement

`isReduced_delWordAt`: if `L` is a reduced word, then `delWordAt T c a L` is reduced,

which in fact needs no closure hypothesis on `L`.

The reducedness is proved by induction on `L`, the induction invariant being
`isReduced_cons_delWordAt`: the deleted word of `L` prepended by any traversal `p` which is
*compatible* with the first deleted traversal of `L` (i.e. the successor hypothesis `hp` below) is
reduced.  The successor hypothesis is supplied by the *local lemma*
`not_cancel_trav_of_middle_mem`: for a reduced word `x :: L₁ ++ y :: L₂`, if all the traversals of
the middle word `L₁` (read from the level reached after `x`) lie in `T`, then the traversal of `x`
and the traversal of `y` do not cancel.  Its proof is the heart of the matter:

* if they cancelled, the middle walk would be closed (`coverTgt_eq_coverSrc_of_coverEdge_eq` gives
  `lsig c L₁ = 0`) and would have all its edges in `T` and no immediate backtrack
  (`noBT_of_isReduced_decor`), so `forestUniq_closed_empty` would force `L₁ = []`;
* but then the two traversals are *consecutive* letters of the reduced decorated word
  `decor c v (x :: y :: L₂)`, which is impossible.

The structure of the first deleted traversal of a deleted word is proved here as the private lemma
`firstMarked_local` (either the deleted word is empty, or it is the traversal of a letter whose
predecessors in the word all lie in `T`, followed by the deleted word of the remaining tail).

The auxiliary facts used are proved in parallel by colleagues in

* `Submission/Work/OROneRel/forestUniq_closed_empty` -- a closed walk in a forest with no immediate
  backtrack is trivial;
* `Submission/Work/OROneRel/isReduced_decor_iff` -- the decoration of a word is reduced iff the word
  is;
* `Submission/Work/OROneRel/noBT_of_isReduced_decor` -- a reduced decorated word has no immediate
  backtrack;
* `Submission/Work/OROneRel/coverTgt_eq_coverSrc_of_coverEdge_eq` -- two traversals of the same edge
  in opposite directions join up;
* `Submission/Work/OROneRel/delWordAt_append` -- the deleted word is additive over concatenations.
-/
import Mathlib
import Submission.Work.OROneRel.delWordDefs
import Submission.Work.OROneRel.delWordWalkDefs
import Submission.Work.OROneRel.forestUniq_closed_empty
import Submission.Work.OROneRel.isReduced_decor_iff
import Submission.Work.OROneRel.noBT_of_isReduced_decor
import Submission.Work.OROneRel.coverTgt_eq_coverSrc_of_coverEdge_eq
import Submission.Work.OROneRel.delWordAt_append

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### The first deleted traversal -/

private theorem lsig_cons_dw (c : α → ℤ) (p : α × Bool) (L : List (α × Bool)) :
    lsig c (p :: L) = linc c p + lsig c L := by
  obtain ⟨x, b⟩ := p
  cases b <;> simp [lsig, linc]

/-- **The first deleted traversal of a deleted word.**  Either the deleted word is empty, or it
begins with the traversal of a letter `y` such that `L = L₁ ++ y :: L₂`, every traversal of `L₁` is
inside `T`, and the rest of the deleted word is the deleted word of `L₂` read from the level reached
after the traversal of `y`. -/
private theorem firstMarked_local (T : Set (α × ℤ)) (c : α → ℤ) (a : ℤ) (L : List (α × Bool)) :
    delWordAt T c a L = [] ∨
      ∃ (L₁ : List (α × Bool)) (y : α × Bool) (L₂ : List (α × Bool)),
        L = L₁ ++ y :: L₂ ∧
        (∀ m ∈ decor c a L₁, coverEdge m ∈ T) ∧
        delWordAt T c a L =
          trav c (a + lsig c L₁) y ::
            delWordAt T c (a + lsig c L₁ + linc c y) L₂ := by
  induction L generalizing a with
  | nil => exact Or.inl (by simp)
  | cons p L ih =>
    by_cases h : coverEdge (trav c a p) ∈ T
    · rw [delWordAt_cons_of_mem T c a p L h]
      rcases ih (a + linc c p) with hnil | ⟨L₁, y, L₂, hL, hT, hdel⟩
      · exact Or.inl hnil
      · refine Or.inr ⟨p :: L₁, y, L₂, ?_, ?_, ?_⟩
        · rw [hL, List.cons_append]
        · rw [decor_cons]
          intro m hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact h
          · exact hT m hm
        · rw [hdel]
          have hlev : (a + linc c p) + lsig c L₁ = a + lsig c (p :: L₁) := by
            rw [lsig_cons_dw]; ring
          rw [hlev]
    · rw [delWordAt_cons_of_notMem T c a p L h]
      refine Or.inr ⟨[], p, L, by simp, ?_, ?_⟩
      · intro m hm
        simp [decor] at hm
      · simp [lsig]

/-! ### The local lemma -/

/-- **The local lemma.**  In a reduced word `x :: L₁ ++ y :: L₂`, if all the traversals of the
middle word `L₁` (read from the level `v + linc c x` reached after the traversal of `x` at level
`v`) lie in the forest `T`, then the traversal of `x` and the traversal of `y` do not cancel. -/
theorem not_cancel_trav_of_middle_mem (c : α → ℤ) (T : Set (α × ℤ)) (hforest : ForestUniq c T)
    {x y : α × Bool} {v : ℤ} {L₁ L₂ : List (α × Bool)}
    (hred : FreeGroup.IsReduced (x :: L₁ ++ y :: L₂))
    (hT : ∀ m ∈ decor c (v + linc c x) L₁, coverEdge m ∈ T) :
    ¬ (coverEdge (trav c v x) = coverEdge (trav c (v + linc c x + lsig c L₁) y) ∧
        (trav c v x).2 ≠ (trav c (v + linc c x + lsig c L₁) y).2) := by
  rintro ⟨h1, h2⟩
  -- the middle walk is closed
  have hmid0 : lsig c L₁ = 0 := by
    have hjoin := coverTgt_eq_coverSrc_of_coverEdge_eq c h1 h2
    rw [coverTgt_trav, coverSrc_trav] at hjoin
    omega
  -- hence the middle word is empty
  have hmid : L₁ = [] := by
    refine forestUniq_closed_empty c T hforest hmid0 hT ?_
    exact noBT_of_isReduced_decor c (v + linc c x)
      ((isReduced_decor_iff c (v + linc c x) L₁).mpr
        (hred.infix ⟨[x], y :: L₂, by simp⟩))
  subst hmid
  simp only [lsig, List.map_nil, List.sum_nil, add_zero] at h1 h2
  -- the two traversals are consecutive letters of a reduced decorated word
  have hdec : FreeGroup.IsReduced (trav c v x :: trav c (v + linc c x) y ::
      decor c (v + linc c x + linc c y) L₂) := by
    have h0 : FreeGroup.IsReduced (decor c v (x :: y :: L₂)) :=
      (isReduced_decor_iff c v (x :: y :: L₂)).mpr (by simpa using hred)
    rwa [decor_cons, decor_cons] at h0
  have hrel := (FreeGroup.isReduced_cons_cons.mp hdec).1
  exact h2 (hrel h1)

/-! ### The induction invariant -/

/-- **The induction invariant.**  If `L` is reduced and the traversal `p` is compatible with the
first deleted traversal of `L` (the hypothesis `hp`), then the deleted word of `L` prepended by `p`
is reduced. -/
theorem isReduced_cons_delWordAt (T : Set (α × ℤ)) (c : α → ℤ) (hforest : ForestUniq c T)
    (L : List (α × Bool)) :
    FreeGroup.IsReduced L → ∀ (a : ℤ) (p : (α × ℤ) × Bool),
      (∀ (c' : (α × ℤ) × Bool) (K : List ((α × ℤ) × Bool)),
        delWordAt T c a L = c' :: K → p.1 = c'.1 → p.2 = c'.2) →
      FreeGroup.IsReduced (p :: delWordAt T c a L) := by
  induction L with
  | nil =>
    intro _ a p _
    simpa using (FreeGroup.IsReduced.singleton (a := p))
  | cons y L ih =>
    intro hred a p hp
    have htailred : FreeGroup.IsReduced L := hred.infix ⟨[y], [], by simp⟩
    by_cases hmem : coverEdge (trav c a y) ∈ T
    · rw [delWordAt_cons_of_mem T c a y L hmem]
      refine ih htailred (a + linc c y) p ?_
      intro c' K hK h1
      exact hp c' K (by rw [← hK, delWordAt_cons_of_mem T c a y L hmem]) h1
    · rw [delWordAt_cons_of_notMem T c a y L hmem]
      have hstep : p.1 = (trav c a y).1 → p.2 = (trav c a y).2 :=
        hp (trav c a y) (delWordAt T c (a + linc c y) L)
          (by rw [delWordAt_cons_of_notMem T c a y L hmem])
      have htail : FreeGroup.IsReduced (trav c a y :: delWordAt T c (a + linc c y) L) :=
        ih htailred (a + linc c y) (trav c a y) (by
          intro c' K hK h1
          rcases firstMarked_local T c (a + linc c y) L with
            hnil | ⟨L₁', y', L₂', hL', hT', hdel'⟩
          · rw [hnil] at hK
            exact absurd hK (by simp)
          · rw [hdel'] at hK
            obtain rfl : c' = trav c (a + linc c y + lsig c L₁') y' :=
              (List.cons.inj hK).1.symm
            by_contra h2'
            exact not_cancel_trav_of_middle_mem c T hforest (x := y) (y := y') (v := a)
              (L₁ := L₁') (L₂ := L₂')
              (hred.infix ⟨[], [], by rw [hL']; simp⟩) hT' ⟨h1, h2'⟩)
      rw [FreeGroup.IsReduced] at htail ⊢
      refine List.IsChain.cons htail ?_
      intro z hz
      rw [List.head?_cons] at hz
      obtain rfl := Option.mem_some_iff.mp hz
      exact hstep

/-! ### Reducedness of the deleted word -/

/-- **The deleted word of a reduced word is reduced.**  No closure hypothesis on `L` is needed. -/
theorem isReduced_delWordAt (T : Set (α × ℤ)) (c : α → ℤ) (hforest : ForestUniq c T)
    (L : List (α × Bool)) (hred : FreeGroup.IsReduced L) (a : ℤ) :
    FreeGroup.IsReduced (delWordAt T c a L) := by
  rcases firstMarked_local T c a L with hnil | ⟨L₁, y, L₂, hL, hT, hdel⟩
  · rw [hnil]
    exact FreeGroup.IsReduced.nil
  · rw [hdel]
    refine isReduced_cons_delWordAt T c hforest L₂
      (hred.infix ⟨L₁ ++ [y], [], by rw [hL]; simp⟩)
      (a + lsig c L₁ + linc c y) (trav c (a + lsig c L₁) y) ?_
    intro c' K hK h1
    rcases firstMarked_local T c (a + lsig c L₁ + linc c y) L₂ with
      hnil | ⟨L₁', y', L₂', hL', hT', hdel'⟩
    · rw [hnil] at hK
      exact absurd hK (by simp)
    · rw [hdel'] at hK
      obtain rfl : c' = trav c (a + lsig c L₁ + linc c y + lsig c L₁') y' :=
        (List.cons.inj hK).1.symm
      by_contra h2'
      exact not_cancel_trav_of_middle_mem c T hforest (x := y) (y := y') (v := a + lsig c L₁)
        (L₁ := L₁') (L₂ := L₂')
        (hred.infix ⟨L₁, [], by rw [hL, hL']; simp⟩) hT' ⟨h1, h2'⟩

/-! ### Cyclic reducedness -/

/-- A word is cyclically reduced exactly when its doubling is reduced. -/
theorem isCyclicallyReduced_iff_isReduced_append_self {α : Type u} {L : List (α × Bool)} :
    FreeGroup.IsCyclicallyReduced L ↔ FreeGroup.IsReduced (L ++ L) := by
  simp only [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]
  rw [List.isChain_append]
  tauto

theorem delWord_isCyclicallyReduced {α : Type u} [DecidableEq α] (c : α → ℤ) (T : Set (α × ℤ))
    {w : List (α × Bool)} (hred : FreeGroup.IsReduced w)
    (hcyc : FreeGroup.IsCyclicallyReduced w) (h0 : lsig c w = 0) (hforest : ForestUniq c T) :
    FreeGroup.IsCyclicallyReduced (delWord T c w) := by
  have hww : FreeGroup.IsReduced (w ++ w) :=
    isCyclicallyReduced_iff_isReduced_append_self.mp hcyc
  have hdel : FreeGroup.IsReduced (delWord T c (w ++ w)) := by
    rw [delWord_eq_delWordAt]
    exact isReduced_delWordAt T c hforest (w ++ w) hww 0
  have hsplit : delWord T c (w ++ w) = delWord T c w ++ delWord T c w := by
    rw [delWord_eq_delWordAt T c (w ++ w), delWordAt_append]
    rw [h0, add_zero]
    rfl
  rw [hsplit] at hdel
  exact isCyclicallyReduced_iff_isReduced_append_self.mpr hdel

end Work.OROneRel
