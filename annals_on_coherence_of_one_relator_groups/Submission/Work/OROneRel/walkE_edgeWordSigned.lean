import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.mk_expand
import Submission.Work.OROneRel.decor_pow_flatMap
import Submission.Work.OROneRel.coedgeBase
import Submission.Work.OROneRel.decor_invRev

namespace Work.OROneRel

/-- The decoration of a single positive letter: reading `(a, true)` from the level `i` decorates
it at the same level. -/
theorem walkE_decor_singleton_true {α : Type*} (c : α → ℤ) (i : ℤ) (a : α) :
    decor c i [(a, true)] = [((a, i), true)] := rfl

/-- **The loop word of an edge of the window walks inside the window.**

If the edge `e = (x,i)` lies in the window `[lo,hi]` and the two gauge words `wordOf (W i)` and
`wordOf (W (i + c x))` walk inside the window (hypotheses `h1`, `h2`), then so does the loop word
`edgeWord W c e = wordOf (W i) ++ [(x,true)] ++ wordOf ((W (i + c x))⁻¹)`: the first block is `h1`,
the middle traverses the edge `e` itself, and the last block is the mirror image of `h2` (its
decoration is `decor c 0 (wordOf (W (i + c x)))` reversed with the booleans flipped and read at
level `i + c x`).  The level identifications `i` and `i + c x` come from `hc1`, `hc2`. -/
theorem walkE_edgeWord {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (e : α × ℤ) (hE : e ∈ winE c lo hi)
    (h1 : ∀ p ∈ decor c 0 (wordOf (Wt e.2)), coverEdge p ∈ winE c lo hi)
    (h2 : ∀ p ∈ decor c 0 (wordOf (Wt (e.2 + c e.1))), coverEdge p ∈ winE c lo hi)
    (hc1 : (cohom c (Wt e.2)).toAdd = e.2)
    (hc2 : (cohom c (Wt (e.2 + c e.1))).toAdd = e.2 + c e.1) :
    ∀ p ∈ decor c 0 (edgeWord Wt c e), coverEdge p ∈ winE c lo hi := by
  have hA : lsig c (wordOf (Wt e.2)) = e.2 := by
    rw [CoedgeBase.lsig_wordOf, hc1]
  have hL : lsig c (wordOf (Wt (e.2 + c e.1))) = e.2 + c e.1 := by
    rw [CoedgeBase.lsig_wordOf, hc2]
  -- The decoration of the loop word, split into the three blocks.
  have hdec : decor c 0 (edgeWord Wt c e) =
      decor c 0 (wordOf (Wt e.2)) ++ [((e.1, e.2), true)]
        ++ (decor c 0 (wordOf (Wt (e.2 + c e.1)))).reverse.map
            (fun p : (α × ℤ) × Bool => (p.1, !p.2)) := by
    unfold edgeWord
    rw [decor_append]
    rw [zero_add, CoedgeBase.lsig_append, hA, CoedgeBase.lsig_singleton_true]
    rw [decor_append]
    rw [zero_add, hA, walkE_decor_singleton_true]
    rw [wordOf_inv, decor_invRev_flip, hL, sub_self]
  have hflip : ∀ q ∈ (decor c 0 (wordOf (Wt (e.2 + c e.1)))).reverse.map
      (fun p : (α × ℤ) × Bool => (p.1, !p.2)), coverEdge q ∈ winE c lo hi := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
    rw [List.mem_reverse] at hp
    exact h2 p hp
  intro p hp
  rw [hdec] at hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact h1 p hp
    · rw [List.mem_singleton] at hp
      rw [hp]
      exact hE
  · exact hflip p hp

/-- The loop word of an edge has vanishing weight: the weight of its initial gauge word is the
source level, the traversed letter contributes `c x`, and the reversed final gauge word contributes
the negative of the target level. -/
theorem walkE_lsig_edgeWord {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ)
    (hc1 : (cohom c (Wt e.2)).toAdd = e.2)
    (hc2 : (cohom c (Wt (e.2 + c e.1))).toAdd = e.2 + c e.1) :
    lsig c (edgeWord Wt c e) = 0 := by
  have hA : lsig c (wordOf (Wt e.2)) = e.2 := by
    rw [CoedgeBase.lsig_wordOf, hc1]
  have hLi : lsig c (wordOf (Wt (e.2 + c e.1))⁻¹) = -(e.2 + c e.1) := by
    rw [CoedgeBase.lsig_wordOf_inv, CoedgeBase.lsig_wordOf, hc2]
  unfold edgeWord
  rw [CoedgeBase.lsig_append, CoedgeBase.lsig_append, hA, CoedgeBase.lsig_singleton_true, hLi]
  ring

theorem walkE_edgeWordSigned {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (e : α × ℤ) (b : Bool) (hE : e ∈ winE c lo hi)
    (h1 : ∀ p ∈ decor c 0 (wordOf (Wt e.2)), coverEdge p ∈ winE c lo hi)
    (h2 : ∀ p ∈ decor c 0 (wordOf (Wt (e.2 + c e.1))), coverEdge p ∈ winE c lo hi)
    (hc1 : (cohom c (Wt e.2)).toAdd = e.2)
    (hc2 : (cohom c (Wt (e.2 + c e.1))).toAdd = e.2 + c e.1) :
    ∀ p ∈ decor c 0 (edgeWordSigned Wt c e b), coverEdge p ∈ winE c lo hi := by
  have hpos := walkE_edgeWord Wt c lo hi e hE h1 h2 hc1 hc2
  have hlsig0 := walkE_lsig_edgeWord Wt c e hc1 hc2
  cases b
  · intro p hp
    rw [show edgeWordSigned Wt c e false = FreeGroup.invRev (edgeWord Wt c e) from by
      simp [edgeWordSigned]] at hp
    rw [decor_invRev_flip, hlsig0, sub_zero] at hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    rw [List.mem_reverse] at hq
    exact hpos q hq
  · intro p hp
    rw [show edgeWordSigned Wt c e true = edgeWord Wt c e from by simp [edgeWordSigned]] at hp
    exact hpos p hp

end Work.OROneRel
