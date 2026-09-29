import Mathlib
import Submission.Work.MainP.crtJoinDefs
import Submission.Work.MainP.crtDefs

/-!
# `crtJoinWord` — the combinatorial (glyph-level) bookkeeping

This file collects the pure list facts that the `Eval`-level proof of `Work.MainP.crtJoinWord`
relies on: the encoding of a zipped list of values unfolds to the `glyph`-level interleaving
description `outGlyphs`, and the three glyph-level stack descriptions (`listEncR`, `bufReg`,
`cntReg`) have the lengths needed for the cost bounds.  Finally every value encoding is a
well-formed pending-subtree word and nonempty.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Lenient-then-physical order: one `zipWith` step -/

/-- Swapping the two lists of a `zipWith` while writing the head glyphs in the physical order:
`zipWith (C :: C :: w ++ x)` over `(xs, ws)` is `zipWith ([C,C] ++ · ++ ·)` over `(ws, xs)`. -/
theorem zipWith_cons_cons_swap (xs ws : List Val) :
    List.zipWith (fun x w => [Glyph.cons, Glyph.cons] ++ HvdH.Val.enc w ++ HvdH.Val.enc x) xs ws =
      List.zipWith (fun w g => [Glyph.cons, Glyph.cons] ++ w ++ g)
        (List.map HvdH.Val.enc ws) (List.map HvdH.Val.enc xs) := by
  rw [List.zipWith_map_left, List.zipWith_map_right]
  exact List.zipWith_comm

/-- The `cons` glyph prepended to the encodings of `zipRec xs ws` is the physical pair encoding
`[cons, cons] ++ w.enc ++ x.enc`. -/
theorem map_cons_map_enc_zip (xs ws : List Val) :
    List.map (fun g => Glyph.cons :: g) (List.map HvdH.Val.enc (zipRec xs ws)) =
      List.zipWith (fun x w => [Glyph.cons, Glyph.cons] ++ HvdH.Val.enc w ++ HvdH.Val.enc x) xs ws := by
  induction xs generalizing ws with
  | nil => cases ws <;> simp [zipRec]
  | cons x xs ih =>
    cases ws with
    | nil => simp [zipRec]
    | cons w ws =>
      simp only [zipRec, List.zipWith_cons_cons, List.map_cons] at ih ⊢
      rw [ih]
      simp only [HvdH.Val.enc, List.cons_append]
      rfl

/-! ## Lengths of the glyph-level descriptions -/

theorem listEncR_length (Gs : List (List Glyph)) :
    (listEncR Gs).length = (Gs.map List.length).sum + Gs.length + 1 := by
  induction Gs with
  | nil => simp [listEncR]
  | cons g gs ih =>
      simp [listEncR_cons, ih, List.length_append]
      ring

theorem bufReg_length (Gs : List (List Glyph)) :
    (bufReg Gs).length = (Gs.map List.length).sum := by
  simp [bufReg, List.length_flatten]

theorem cntReg_length (Gs : List (List Glyph)) :
    (cntReg Gs).length = (Gs.map List.length).sum + Gs.length := by
  induction Gs with
  | nil => simp [cntReg]
  | cons g gs ih =>
      simp [cntReg_cons, ih, List.length_append]
      ring

theorem pendOK_enc_one (x : HvdH.Val) : HvdH.PendOK x.enc 1 ∧ x.enc ≠ [] := by
  refine ⟨HvdH.pendOK_enc x 1 (by norm_num), ?_⟩
  intro hnil
  have h1 := one_le_vsz x
  simp [HvdH.vsz] at h1
  rw [hnil] at h1
  simp at h1

/-- The encoding of `ofList (zipRec xs ws)` is the glyph-level interleaving of the encodings. -/
theorem ofList_zipRec_enc (xs ws : List Val) :
    (HvdH.ofList (zipRec xs ws)).enc =
      outGlyphs (List.map HvdH.Val.enc ws) (List.map HvdH.Val.enc xs) := by
  rw [listEncR_map_enc]
  unfold listEncR outGlyphs
  rw [map_cons_map_enc_zip, zipWith_cons_cons_swap]

theorem crtJoinAlg (xs ws : List HvdH.Val) (h : xs.length = ws.length) :
    (HvdH.ofList (Work.MainP.zipRec xs ws)).enc =
        Work.MainP.outGlyphs (ws.map HvdH.Val.enc) (xs.map HvdH.Val.enc) ∧
      (∀ Gs : List (List HvdH.Glyph),
        (Work.MainP.listEncR Gs).length = (Gs.map List.length).sum + Gs.length + 1) ∧
      (∀ Gs : List (List HvdH.Glyph), (Work.MainP.bufReg Gs).length = (Gs.map List.length).sum) ∧
      (∀ Gs : List (List HvdH.Glyph),
        (Work.MainP.cntReg Gs).length = (Gs.map List.length).sum + Gs.length) ∧
      (∀ x ∈ xs ++ ws, HvdH.PendOK x.enc 1 ∧ x.enc ≠ []) := by
  refine ⟨ofList_zipRec_enc xs ws, listEncR_length, bufReg_length, cntReg_length, ?_⟩
  intro x _
  exact pendOK_enc_one x

end Work.MainP
