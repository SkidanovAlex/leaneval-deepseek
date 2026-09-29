import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.stripFalses_append_cons
import Submission.Work.IntLib.partBlk_marker_step
import Submission.Work.IntLib.divmod_succ

namespace Work.IntLib

open HvdH

/-! ### Bookkeeping helpers

List concatenation `++` is left-associative, while unfolding `outOrder` (whose definition is
written with `++`) produces a right-associated concatenation.  `partBlk_marker_step'` is the
right-associated form of the delegated lemma `partBlk_marker_step`; `flatMap_range_succ` splits
`flatMap` over `range (n+1)`; the two `stripFalses` lemmas record that the group marker
`cons`/`pos` blocks the deletion of trailing `bit false` glyphs. -/

/-- Right-associated form of `partBlk_marker_step`, i.e. the shape in which that lemma is met
after unfolding `outOrder`. -/
lemma partBlk_marker_step' (ps : List Bool) (b k : ℕ) (hb : 1 ≤ b) (hk : k < ps.length) :
    (if k % b = 0 then [] else Work.IntLib.partBlk ps b k) ++
        ((if k % b = 0 then [HvdH.Glyph.cons, HvdH.Glyph.pos] else []) ++
          [HvdH.Glyph.bit (ps.getD k false)]) =
      [HvdH.Glyph.cons, HvdH.Glyph.pos] ++
        ((ps.drop (b * (k / b))).take (k % b + 1)).map HvdH.Glyph.bit := by
  rw [← List.append_assoc]
  exact partBlk_marker_step ps b k hb hk

/-- Splitting off the last index of `List.range`. -/
lemma flatMap_range_succ {α : Type*} (f : ℕ → List α) (n : ℕ) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [show n + 1 = n.succ from rfl, List.range_succ, List.flatMap_append]
  simp

/-- `stripFalses` on a list headed by a glyph other than `bit false`. -/
lemma stripFalses_cons (a : Glyph) (M : List Glyph) (ha : a ≠ Glyph.bit false) :
    Work.IntLib.stripFalses (a :: M) = a :: Work.IntLib.stripFalses M := by
  rw [show (a :: M) = ([] : List Glyph) ++ a :: M from rfl]
  rw [stripFalses_append_cons (h := a) ha]
  rfl

/-- The group marker `cons`/`pos` blocks `stripFalses`: only the part to its right is stripped. -/
lemma stripFalses_marker (X M : List Glyph) :
    Work.IntLib.stripFalses (X ++ ([Glyph.cons, Glyph.pos] ++ M)) =
      X ++ ([Glyph.cons, Glyph.pos] ++ Work.IntLib.stripFalses M) := by
  have h1 : X ++ ([Glyph.cons, Glyph.pos] ++ M) = X ++ Glyph.cons :: (Glyph.pos :: M) := by simp
  rw [h1]
  rw [stripFalses_append_cons (h := Glyph.cons) (by decide)]
  rw [stripFalses_cons (Glyph.pos) M (by decide)]
  rfl

theorem outOrderStepProved (ps : List Bool) (b k : ℕ) (hb : 1 ≤ b) (hk : k < ps.length) :
    Work.IntLib.outOrder ps b (k + 1) =
      (if (k + 1) % b = 0 then
        Work.IntLib.stripFalses (Work.IntLib.outOrder ps b k ++
          (if k % b = 0 then [HvdH.Glyph.cons, HvdH.Glyph.pos] else []) ++
          [HvdH.Glyph.bit (ps.getD k false)]) ++ [HvdH.Glyph.iend]
       else
        Work.IntLib.outOrder ps b k ++
          (if k % b = 0 then [HvdH.Glyph.cons, HvdH.Glyph.pos] else []) ++
          [HvdH.Glyph.bit (ps.getD k false)]) := by
  obtain ⟨hdiv, hmod⟩ := divmod_succ b k hb
  have hne : k % b + 1 ≠ 0 := Nat.add_one_ne_zero _
  by_cases hc : k % b + 1 = b
  · -- `k % b + 1 = b`: the new bit completes a group, which is then closed with `iend`
    have hmod0 : (k + 1) % b = 0 := by rw [hmod, if_pos hc]
    have hdiv2 : (k + 1) / b = k / b + 1 := by rw [hdiv, if_pos hc]
    have hblk : Work.IntLib.blk ps b (k / b) =
        [HvdH.Glyph.cons, HvdH.Glyph.pos] ++
          Work.IntLib.stripFalses (((ps.drop (b * (k / b))).take b).map HvdH.Glyph.bit) ++
          [HvdH.Glyph.iend] := rfl
    unfold Work.IntLib.outOrder
    simp only [hdiv2, if_pos hmod0, List.append_nil, List.append_assoc]
    rw [flatMap_range_succ]
    rw [partBlk_marker_step' ps b k hb hk]
    rw [hc, stripFalses_marker, hblk]
    simp only [List.append_assoc]
  · -- `k % b + 1 ≠ b`: the new bit merely extends the group in progress
    have hmod_ne : (k + 1) % b ≠ 0 := by rw [hmod, if_neg hc]; exact hne
    have hdiv_k : (k + 1) / b = k / b := by rw [hdiv, if_neg hc]
    have hpart : Work.IntLib.partBlk ps b (k + 1) =
        [HvdH.Glyph.cons, HvdH.Glyph.pos] ++
          ((ps.drop (b * (k / b))).take (k % b + 1)).map HvdH.Glyph.bit := by
      rw [Work.IntLib.partBlk, hdiv_k, hmod, if_neg hc]
    unfold Work.IntLib.outOrder
    simp only [hdiv_k, if_neg hmod_ne, hpart, List.append_assoc]
    rw [partBlk_marker_step' ps b k hb hk]

end Work.IntLib
