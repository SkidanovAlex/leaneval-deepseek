import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.stripZeros_range_eval

/-!
# `eval_stripZeros`: `stripZeros` on a `bitsG l ++ T :: bk` region

`Work.IntLib.stripZeros k T r` walks down the region of stack `k` above the frame marker `T`,
dropping the maximal prefix of `Glyph.bit false` glyphs, then pops the first glyph that is not a
`false` bit and pushes it back (`T` itself is a dead parameter: it is the marker of the region,
which the loop never reaches because it stops at the next `T` anyway).

Bit strings are represented in this development as `List Bool`, least significant bit first
(`Work.IntLib.bitsG`).  On the region `bitsG l ++ T :: bk` the procedure therefore removes the
leading `false` bits of `l`, leaving

  `s'.stk k = (bitsG l).dropWhile (fun g => g = Glyph.bit false) ++ T :: bk`,

in `2 * (number of dropped glyphs) + 6` steps, hence in at most `2 * (l.length + 1) + 6` steps.
Only stack `k` is modified; registers are clobbered freely, and everything below `T` (namely `bk`)
is untouched.  The hypotheses `hT` and `hbT` say that the marker `T` is neither `eos` nor a bit
glyph, so that the loop stops at `T` rather than running past it (a `true` bit of `l` may stop it
even earlier, of course: `dropWhile` keeps whatever the first non-`false` glyph is).

The corresponding raw `Eval` statement, for an arbitrary prefix `e` of `false` bits followed by a
`rest` whose head is a genuine glyph, is `Work.IntLib.stripZeros_range_eval`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- If `dropWhile p` stops at `a`, then `a` does not satisfy `p`. -/
theorem dropWhile_eq_cons_not {α : Type*} {p : α → Bool} :
    ∀ (l : List α) {a : α} {t : List α}, l.dropWhile p = a :: t → ¬ (p a = true) := by
  intro l
  induction l with
  | nil => intro a t h; simp at h
  | cons b bs ih =>
    intro a t h
    rw [List.dropWhile_cons] at h
    by_cases hb : p b = true
    · rw [ite_eq_left hb] at h
      exact ih h
    · rw [ite_eq_right hb] at h
      simp only [List.cons.injEq] at h
      rw [← h.1]
      exact hb

theorem eval_stripZeros (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (r : HvdH.Reg)
    (l : List Bool) (bk : List HvdH.Glyph) (s : HvdH.State)
    (hT : T ≠ HvdH.Glyph.eos) (hbT : ∀ b : Bool, HvdH.Glyph.bit b ≠ T)
    (hk : s.stk k = Work.IntLib.bitsG l ++ T :: bk) :
    ∃ s' n, HvdH.Eval main (Work.IntLib.stripZeros k T r) s s' n ∧
      n ≤ 2 * (l.length + 1) + 6 ∧
      s'.stk k = (Work.IntLib.bitsG l).dropWhile (fun g => g = HvdH.Glyph.bit false) ++ T :: bk ∧
      ∀ j : HvdH.Stk, j ≠ k → s'.stk j = s.stk j := by
  let p : Glyph → Bool := fun g => g = Glyph.bit false
  -- the prefix of `false` bits is `takeWhile`, and the glyph that stops the loop is its head
  have he : ∀ x ∈ (bitsG l).takeWhile p, x = Glyph.bit false := by
    intro x hx
    simpa [p] using List.mem_takeWhile_imp hx
  have hsplit : (bitsG l).takeWhile p ++ (bitsG l).dropWhile p = bitsG l :=
    List.takeWhile_append_dropWhile
  -- the glyph that stops the loop is a genuine glyph (not `eos`, not a `false` bit)
  have hrest_ne : ((bitsG l).dropWhile p ++ T :: bk).headD Glyph.eos ≠ Glyph.bit false := by
    rcases hgs : (bitsG l).dropWhile p with _ | ⟨g, gs⟩
    · simp only [List.nil_append, List.headD_cons]
      intro hcon
      exact hbT false hcon.symm
    · simp only [List.cons_append, List.headD_cons]
      intro hcon
      have hgg : ¬ (p g = true) := dropWhile_eq_cons_not (bitsG l) hgs
      exact hgg (by simp [p, hcon])
  have heos : ((bitsG l).dropWhile p ++ T :: bk).headD Glyph.eos ≠ Glyph.eos := by
    rcases hgs : (bitsG l).dropWhile p with _ | ⟨g, gs⟩
    · simp only [List.nil_append, List.headD_cons]
      exact hT
    · simp only [List.cons_append, List.headD_cons]
      intro hcon
      have hgmem : g ∈ (bitsG l).dropWhile p := by rw [hgs]; exact List.mem_cons_self
      obtain ⟨b, -, hb⟩ := List.mem_map.mp (List.Sublist.mem hgmem (List.dropWhile_sublist p))
      exact absurd (hb.trans hcon) (by simp)
  have hstk : s.stk k = (bitsG l).takeWhile p ++ ((bitsG l).dropWhile p ++ T :: bk) := by
    calc s.stk k = bitsG l ++ T :: bk := hk
      _ = ((bitsG l).takeWhile p ++ (bitsG l).dropWhile p) ++ T :: bk := by rw [hsplit]
      _ = (bitsG l).takeWhile p ++ ((bitsG l).dropWhile p ++ T :: bk) := List.append_assoc ..
  have hmain := stripZeros_range_eval main k T r ((bitsG l).takeWhile p)
    ((bitsG l).dropWhile p ++ T :: bk) s he hrest_ne heos hstk
  refine ⟨⟨Function.update s.reg r (((bitsG l).dropWhile p ++ T :: bk).headD Glyph.eos),
    Function.update s.stk k ((bitsG l).dropWhile p ++ T :: bk)⟩,
    2 * ((bitsG l).takeWhile p).length + 6, hmain, ?_, ?_, ?_⟩
  · have hlen : ((bitsG l).takeWhile p).length ≤ l.length := by
      have hh := List.Sublist.length_le (List.takeWhile_sublist (l := bitsG l) p)
      simpa [bitsG] using hh
    omega
  · exact Function.update_self k _ s.stk
  · intro j hj
    exact Function.update_of_ne hj _ _

end Work.IntLib
