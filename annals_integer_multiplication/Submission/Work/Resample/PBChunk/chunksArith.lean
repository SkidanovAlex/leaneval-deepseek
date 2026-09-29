-- PRIVATE COPY (own namespace, Resample/PB dialect) of `Submission/Work/Layout/chunksArith.lean`.
-- The declarations have been moved from `Work.Layout`/`Work.Resample` into the
-- dedicated namespace `Work.Resample.PBChunk` (with `buildFrameT`/`chunksOfWordT`
-- renamed to `buildFramePB`/`chunksOfWordPB`) so that this module coexists with
-- every other module of the workspace (in particular with `Layout.Take.*` and with
-- `Work.Layout.AA.Defs`).  The proofs are unchanged.
import Mathlib
import Submission.Work.Resample.PBChunk.chunksOfDefs
/-!
# `LayoutLib.chunksOf`: elementary size and index arithmetic

Sizes of lists of values (`vsz (ofList ys)`), sums over flattened lists, and the length of the
`m`-chunks of a list of length divisible by `m`.
-/

set_option autoImplicit false

namespace Work.Resample.PBChunk

open Work.Layout
open HvdH

theorem length_flatten_map_cons (ys : List Val) :
    ((ys.map fun v => Glyph.cons :: v.enc).flatten).length =
      (ys.map fun v => vsz v + 1).sum := by
  induction ys with
  | nil => simp
  | cons v ys ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
        List.sum_cons]
      rw [ih, vsz]

/-- the size of a list value, as a sum -/
theorem vsz_ofList_eq (ys : List Val) :
    vsz (ofList ys) = (ys.map fun v => vsz v + 1).sum + 1 := by
  rw [vsz, enc_ofList_eq, List.length_append, List.length_singleton, length_flatten_map_cons]

theorem sum_map_vsz_succ (C : List Val) :
    (C.map fun v => vsz v + 1).sum = (C.map vsz).sum + C.length := by
  induction C with
  | nil => simp
  | cons v C ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem sum_map_one (l : List ℕ) : (l.map fun _ => (1 : ℕ)).sum = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

theorem sum_map_add' (l : List (List Val)) (f g : List Val → ℕ) :
    (l.map fun C => f C + g C).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons C l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_flatten_map (ch : List (List Val)) (f : Val → ℕ) :
    ((ch.map fun C => (C.map f).sum).sum) = ((ch.flatten).map f).sum := by
  induction ch with
  | nil => simp
  | cons C ch ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append,
        List.sum_append, ih]

theorem sum_map_flatten_length (ch : List (List Val)) :
    (ch.map fun C => C.length).sum = ch.flatten.length := by
  induction ch with
  | nil => simp
  | cons C ch ih => simp only [List.map_cons, List.sum_cons, List.flatten_cons,
      List.length_append, List.length_cons, ih]

/-- the size of the list of chunks -/
theorem vsz_map_ofList_eq (ch : List (List Val)) :
    vsz (ofList (ch.map ofList)) =
      ((ch.map fun C => (C.map vsz).sum + C.length).sum) + 2 * ch.length + 1 := by
  induction ch with
  | nil => simp [vsz_ofList_eq]
  | cons C ch ih =>
      rw [List.map_cons, vsz_ofList_cons, ih, List.map_cons, List.sum_cons, List.length_cons,
        vsz_ofList_eq, sum_map_vsz_succ]
      ring

theorem sum_map_chunk (ch : List (List Val)) :
    ((ch.map fun C => (C.map vsz).sum + C.length).sum)
      = ((ch.flatten).map vsz).sum + ch.flatten.length := by
  induction ch with
  | nil => simp
  | cons C ch ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append,
        List.sum_append, List.length_append, ih]
      ring

/-- the size of the chunk list of `xs` -/
theorem vsz_chunks (xs : List Val) (m : ℕ) (hm : 1 ≤ m) (hdvd : m ∣ xs.length) :
    vsz (ofList (((List.range (xs.length / m)).map (fun i => (xs.drop (i * m)).take m)).map
        ofList)) = vsz (ofList xs) + 2 * (xs.length / m) := by
  have hflat : ((List.range (xs.length / m)).map (fun i => (xs.drop (i * m)).take m)).flatten
      = xs := flatMap_range_chunkAt_eq xs hdvd
  have hlen : ((List.range (xs.length / m)).map (fun i => (xs.drop (i * m)).take m)).length
      = xs.length / m := by simp
  rw [vsz_map_ofList_eq, sum_map_chunk, hflat, hlen, vsz_ofList_eq, sum_map_vsz_succ]
  ring

/-- the length of every `m`-chunk -/
theorem chunk_length {m : ℕ} (hm : 1 ≤ m) {xs : List Val} (hdvd : m ∣ xs.length) :
    ∀ i < xs.length / m, ((xs.drop (i * m)).take m).length = m := by
  intro i hi
  have h1 : i * m + m ≤ xs.length := by
    have h2 : i + 1 ≤ xs.length / m := hi
    have h3 : (i + 1) * m ≤ (xs.length / m) * m := Nat.mul_le_mul_right m h2
    rw [Nat.div_mul_cancel hdvd] at h3
    simpa [Nat.add_mul] using h3
  have h4 : (xs.drop (i * m)).length = xs.length - i * m := List.length_drop ..
  have h5 : m ≤ xs.length - i * m := by omega
  rw [List.length_take, h4]
  omega

end Work.Resample.PBChunk