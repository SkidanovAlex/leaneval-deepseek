import Mathlib
import Submission.Work.Layout.chunksOfDefs
import Submission.Work.Layout.chunksProof

/-!
# `Work.Layout.buildProg`: definitions and pure-list facts

Support module for `Submission/Work/Layout/build_ev.lean` (the outer loop of the chunk builder).

* `EncSeq A` : the glyphs that the element stack `sT` delivers for the list of chunks `A` — the
  chunks are consumed in the order they appear in `A` (head of `A` next), each chunk delivering its
  elements *reversed*, all value encodings flattened.
* `groupCost m c`, `loopCost m A` : the cost bounds of one iteration of the outer loop (on a chunk
  `c` of length `m`) and of the whole loop over `A`.
* head lemmas: the head of a (nonempty) value encoding is never `gSent`, so the loop test on the top
  glyph of `sT` correctly detects the `gSent` sentinel.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## The element sequence delivered by `sT` -/

/-- Glyphs delivered by the element stack `sT` for a list of chunks `A`: the chunks are consumed in
the order they appear in `A` (head of `A` next), each chunk delivering its elements reversed, all
encodings flattened. -/
def EncSeq (A : List (List Val)) : List Glyph := ((A.flatMap List.reverse).map Val.enc).flatten

@[simp] theorem EncSeq_nil : EncSeq ([] : List (List Val)) = [] := rfl

theorem EncSeq_cons (c : List Val) (A : List (List Val)) :
    EncSeq (c :: A) = (c.reverse.map Val.enc).flatten ++ EncSeq A := by
  simp only [EncSeq, List.flatMap_cons, List.map_append, List.flatten_append]

/-- `EncSeq` of the reverse of `ch` is the element sequence of the chunks `ch` in processing order. -/
theorem EncSeq_reverse_eq (ch : List (List Val)) :
    EncSeq ch.reverse = ((elemOrder ch).map Val.enc).flatten := rfl

/-! ## The head of a value encoding is never `gSent` -/

/-- The head of a value encoding (with arbitrary tail) is never `gSent`. -/
theorem headD_enc_append_ne_gSent (v : Val) (B : List Glyph) :
    (v.enc ++ B).headD Glyph.eos ≠ gSent := by
  cases v with
  | int z =>
      by_cases hz : z < 0
      · rw [Val.enc, if_pos hz, List.cons_append, List.headD_cons]
        exact fun h => gSent_ne_neg h.symm
      · rw [Val.enc, if_neg hz, List.cons_append, List.headD_cons]
        exact fun h => gSent_ne_pos h.symm
  | nil =>
      rw [Val.enc, List.singleton_append, List.headD_cons]
      exact fun h => gSent_ne_nil h.symm
  | cons a b =>
      rw [Val.enc, List.cons_append, List.headD_cons]
      exact fun h => gSent_ne_cons h.symm

/-- The head of a nonempty stack of values (with arbitrary tail) is never `gSent`. -/
theorem headD_encs_ne_gSent {vs : List Val} (h : vs ≠ []) (R : List Glyph) :
    (encs vs ++ R).headD Glyph.eos ≠ gSent := by
  match vs with
  | [] => exact absurd rfl h
  | v :: vs' =>
      rw [show encs (v :: vs') = v.enc ++ encs vs' from rfl, List.append_assoc]
      exact headD_enc_append_ne_gSent v (encs vs' ++ R)

/-- The head of `EncSeq (c :: A) ++ R` with `c` nonempty is never `gSent`. -/
theorem EncSeq_headD_ne_gSent {c : List Val} (hc : c ≠ []) (A : List (List Val))
    (R : List Glyph) : (EncSeq (c :: A) ++ R).headD Glyph.eos ≠ gSent := by
  rw [EncSeq_cons, List.append_assoc]
  exact headD_encs_ne_gSent (by simpa using hc) (EncSeq A ++ R)

/-! ## Cost functions -/

/-- Cost bound of one (non-final) iteration of the outer loop, on a chunk `c` of length `m`.
This is the bound obtained from `copy_ev` (`40*(m+1)+40`) and `inner_ev`
(`40*((c.map vsz).sum + m + 1)`) plus the 8 primitive steps of the loop body. -/
def groupCost (m : ℕ) (c : List Val) : ℕ := 40 * (c.map vsz).sum + 80 * m + 128

/-- Cost bound of the whole outer loop over the chunks `A` (each of length `m`): `#A` iterations
plus the final one that detects the sentinel. -/
def loopCost (m : ℕ) (A : List (List Val)) : ℕ := (A.map (groupCost m)).sum + A.length + 4

@[simp] theorem loopCost_nil (m : ℕ) : loopCost m [] = 4 := by simp [loopCost]

theorem loopCost_cons (m : ℕ) (c : List Val) (A : List (List Val)) :
    loopCost m (c :: A) = groupCost m c + loopCost m A + 1 := by
  simp only [loopCost, List.map_cons, List.sum_cons, List.length_cons]
  omega

/-- Sum of the per-chunk costs, bounded by the total element size and the number of elements. -/
theorem sum_groupCost_le (m : ℕ) (l : List (List Val)) :
    (l.map (groupCost m)).sum ≤
      40 * (l.map (fun c => (c.map vsz).sum)).sum + (80 * m + 128) * l.length := by
  induction l with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hc : groupCost m c = 40 * (c.map vsz).sum + (80 * m + 128) := rfl
      rw [hc, Nat.mul_succ, Nat.mul_add]
      omega

/-- The per-chunk cost bound summed over the chunk list, in terms of the total element size. -/
theorem sum_groupCost_le' (m : ℕ) (ch : List (List Val)) :
    (ch.map (groupCost m)).sum ≤
      40 * (ch.map (fun c => (c.map vsz).sum)).sum + (80 * m + 128) * ch.length :=
  sum_groupCost_le m ch

theorem sum_map_const (l : List ℕ) (k : ℕ) : (l.map (fun _ => k)).sum = k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.mul_succ]
      omega

end Work.Layout
