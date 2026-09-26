import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

/-! ## Unpacking the separation list

`Data.Sep.chk` is a Boolean check on one separation certificate; `SepOK` is the componentwise
mathematical content it is supposed to certify (as consumed by the four `*_separates` lemmas).
This file proves that every entry of `Data.sepList` that passes the check really satisfies
`SepOK`.

Three of the four constructors are pure Boolean-unpacking (`Bool.and_eq_true`, `beq_iff_eq`,
`bne_iff_ne`, `List.all_eq_true`).  The exception is the `sym` case, where `SepOK` also asks for
the bounds `a.o ≤ 48`, `b.o ≤ 48` on the two symmorphy orders.  These are *not* implied by
`Data.Sep.chk` (which only rules out non-coboundaries for the primes `≤ 47`, whereas soundness
of the symmorphy-order check needs all prime divisors of `o` to be listed); they are extra
information about the two `.sym` entries of the list, and are recovered from `he` by a finite
kernel check over the list. -/

/-- The `sym`-bound guard on `Data.sepList`: for the `.sym` entries, both symmorphy orders are
`≤ 48`; all other entries pass trivially.  (The two `.sym` entries of `Data.sepList` are
`.sym 49 50` and `.sym 172 173`, both with orders `1` and `2`.) -/
def symBoundOK : Data.Sep → Bool
  | .sym _ _ a b => decide (a.o ≤ 48) && decide (b.o ≤ 48)
  | _ => true

/-- Finite kernel check: every entry of the separation list satisfies `symBoundOK`. -/
theorem sepList_all_symBoundOK : Data.sepList.all symBoundOK = true := by decide +kernel

/-- Unpacking a separation entry: every `e ∈ Data.sepList` passing `Data.Sep.chk` satisfies the
componentwise predicate `SepOK` (defined in `SGsepDefs`).  The four cases are the four
constructors of `Data.Sep` with `Data.Sep.chk` unfolded (`Bool.and_eq_true`, `bne_iff_ne`,
`List.all_eq_true`).  For the `.sym` case the bounds `a.o ≤ 48`, `b.o ≤ 48` are *not* implied by
`Data.Sep.chk` (which only tests the primes `≤ 47`), but they hold for the two `.sym` entries of
`Data.sepList`, so they must be derived from `he : e ∈ Data.sepList` by a finite check over the
list (give them a separate `decide`-checked helper). -/
theorem sepOK_of_chk (e : Data.Sep) (he : e ∈ Data.sepList) (h : Data.Sep.chk e = true) :
    SepOK e := by
  have hb : symBoundOK e = true := List.all_eq_true.mp sepList_all_symBoundOK e he
  cases e with
  | elem k l d t o =>
      simp only [SepOK, Data.Sep.chk, bne_iff_ne] at h ⊢
      exact h
  | sym k l a b =>
      simp only [symBoundOK, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [SepOK, Data.Sep.chk, Bool.and_eq_true, bne_iff_ne] at h ⊢
      exact ⟨h.1.1, h.1.2, hb.1, hb.2, h.2⟩
  | hand k l o hh jm ta tb =>
      simp only [SepOK, Data.Sep.chk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        List.mem_range, bne_iff_ne] at h ⊢
      exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  | pair k l dA tA oA dB tB oB bits la lb =>
      simp only [SepOK, Data.Sep.chk] at h ⊢
      split at h
      · rename_i ca cb hka hkb
        exact ⟨ca, cb, hka, hkb, by simpa using h⟩
      · simp at h

end Work.SGsep
