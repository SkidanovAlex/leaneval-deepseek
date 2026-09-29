import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.SqrtGcd.Basic

/-!
# `stripZeros` on a range of `false` bits

`Work.IntLib.stripZeros k T r` (from `divRaw.lean`) drops the maximal prefix of
`Glyph.bit false` glyphs from the region of stack `k`, leaving the following glyph on top of the
stack.  This file gives the *exact* cost form of that statement for a prefix `e` of `false` bits
followed by a `rest` whose head is neither `false` nor `eos`: the program reaches the expected state
in exactly `2 * e.length + 6` steps.

The `rest.headD eos ≠ eos` hypothesis is what makes the trailing `ite` push the glyph back; the
loop itself pops one glyph too many, and the `ite` restores it.  This mirrors
`Work.IntLib.SG.stripZeros_eval` (`SqrtGcd/Basic.lean`), which is stated for a prefix
`List.replicate zs false` and with `head?` hypotheses; the two bridges below convert between the
two forms.
-/

namespace Work.IntLib

open HvdH

/-- A list of glyphs whose members are all `Glyph.bit false` *is* a replicate. -/
theorem eq_replicate_bit_false {e : List Glyph} (he : ∀ x ∈ e, x = Glyph.bit false) :
    e = List.replicate e.length (Glyph.bit false) := by
  rw [List.eq_replicate_iff]
  exact ⟨rfl, he⟩

/-- A `headD` that is neither `Glyph.bit false` nor `Glyph.eos` has a `head?` that is neither. -/
theorem head?_ne_of_headD_ne {rest : List Glyph} (h1 : rest.headD Glyph.eos ≠ Glyph.bit false)
    (h2 : rest.headD Glyph.eos ≠ Glyph.eos) :
    rest.head? ≠ some (Glyph.bit false) ∧ rest.head? ≠ some Glyph.eos := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases rest with
    | nil => simp at h
    | cons g gs =>
      simp only [List.head?_cons, Option.some.injEq] at h
      simp [h] at h1
  · cases rest with
    | nil => simp at h
    | cons g gs =>
      simp only [List.head?_cons, Option.some.injEq] at h
      simp [h] at h2

theorem stripZeros_range_eval (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (r : HvdH.Reg) :
    ∀ (e rest : List HvdH.Glyph) (s : HvdH.State),
      (∀ x ∈ e, x = HvdH.Glyph.bit false) →
      rest.headD HvdH.Glyph.eos ≠ HvdH.Glyph.bit false →
      rest.headD HvdH.Glyph.eos ≠ HvdH.Glyph.eos →
      s.stk k = e ++ rest →
      HvdH.Eval main (Work.IntLib.stripZeros k T r) s
        ⟨Function.update s.reg r (rest.headD HvdH.Glyph.eos), Function.update s.stk k rest⟩
        (2 * e.length + 6) := by
  intro e rest s he h1 h2 hstk
  obtain ⟨h1', h2'⟩ := head?_ne_of_headD_ne h1 h2
  have he' : (List.replicate e.length false).map HvdH.Glyph.bit = e := by
    rw [List.map_replicate, ← eq_replicate_bit_false he]
  have hstk' : s.stk k = (List.replicate e.length false).map HvdH.Glyph.bit ++ rest := by
    rw [he', hstk]
  have h := SG.stripZeros_eval main k r e.length rest s hstk' h1' h2'
  simpa only [Work.IntLib.stripZeros, SG.stripZeros] using h

end Work.IntLib
