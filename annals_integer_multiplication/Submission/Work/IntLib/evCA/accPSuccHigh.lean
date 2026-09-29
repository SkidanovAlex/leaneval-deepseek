import Mathlib
import Submission.Work.IntLib.evCarryDefs

/-!
# `accPSuccHigh`: the "high" branch of one `routeA` step

`EvC.accP b W hbits LO Os A2s Cs k s` records the accumulators after `k` iterations of the
ripple addition of `hbits` into the window `W`: the first `min b k` produced sum bits sit on `aO`,
the remaining ones on `a2`, and the unary counter `aCW` still holds `b - k` tokens.

Once `b ≤ k` the counter is exhausted, so `routeA` pushes the next sum bit onto `a2` and leaves
both `aO` and `aCW` untouched.  This file proves that the invariant is preserved by that step:
if

* `s'.stk aO = s.stk aO` (nothing finalised this round),
* `s'.stk a2 = bit (sumBit …) :: s.stk a2` (the sum bit went to the high part),
* `s'.stk aCW = s.stk aCW` (no counter token consumed),

then `accP` holds at `k + 1` as well.  The whole content is that `accF` of `k + 1` is `accF` of `k`
with one bit appended, and that appending a bit beyond position `b ≤ k` does not change the `take`
and shifts the `drop` by exactly that bit.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.evCA

open HvdH

/-- `accF` at `k + 1` is `accF` at `k` with the `k`-th sum bit appended. -/
theorem accF_succ (W hbits : List Bool) (k : ℕ) :
    Work.IntLib.EvC.accF W hbits false (k + 1) =
      Work.IntLib.EvC.accF W hbits false k ++
        [Work.IntLib.EvC.sumBit (W.getD k false) (hbits.getD k false)
          (Work.IntLib.EvC.carryC W hbits false k)] := rfl

/-- Appending a bit at position `k ≥ b` leaves the `take b` of `accF` unchanged. -/
theorem accF_take_succ_of_le {W hbits : List Bool} {b k : ℕ} (hbk : b ≤ k) :
    (Work.IntLib.EvC.accF W hbits false (k + 1)).take b =
      (Work.IntLib.EvC.accF W hbits false k).take b := by
  have hlen : b ≤ (Work.IntLib.EvC.accF W hbits false k).length := by
    rw [Work.IntLib.EvC.accF_length]; exact hbk
  rw [accF_succ, Work.IntLib.EvC.take_append_singleton_of_le _ _ hlen]

/-- Appending a bit at position `k ≥ b` moves the `drop b` by exactly that bit, so reversing it
puts the new bit on top. -/
theorem accF_drop_succ_reverse_of_le {W hbits : List Bool} {b k : ℕ} (hbk : b ≤ k) :
    ((Work.IntLib.EvC.accF W hbits false (k + 1)).drop b).reverse =
      Work.IntLib.EvC.sumBit (W.getD k false) (hbits.getD k false)
          (Work.IntLib.EvC.carryC W hbits false k) ::
        ((Work.IntLib.EvC.accF W hbits false k).drop b).reverse := by
  have hlen : b ≤ (Work.IntLib.EvC.accF W hbits false k).length := by
    rw [Work.IntLib.EvC.accF_length]; exact hbk
  rw [accF_succ, Work.IntLib.EvC.drop_append_singleton_of_le _ _ hlen]
  simp

/-- **The "high" branch of one `routeA` step.**  When the unary counter is already exhausted
(`b ≤ k`), the fresh sum bit goes to `a2` and `aO` and the counter are untouched, so the
accumulator invariant `EvC.accP` is preserved. -/
theorem accPSuccHigh (b : ℕ) (W hbits LO : List Bool) (Os A2s Cs : List HvdH.Glyph)
    (k : ℕ) (s s' : HvdH.State) (hbk : b ≤ k)
    (hacc : Work.IntLib.EvC.accP b W hbits LO Os A2s Cs k s)
    (hO : s'.stk Work.IntLib.aO = s.stk Work.IntLib.aO)
    (h2 : s'.stk Work.IntLib.a2 = HvdH.Glyph.bit
        (Work.IntLib.EvC.sumBit (W.getD k false) (hbits.getD k false)
          (Work.IntLib.EvC.carryC W hbits false k)) :: s.stk Work.IntLib.a2)
    (hCW : s'.stk Work.IntLib.aCW = s.stk Work.IntLib.aCW) :
    Work.IntLib.EvC.accP b W hbits LO Os A2s Cs (k + 1) s' := by
  obtain ⟨hOa, h2a, hCWa⟩ := hacc
  have hbk0 : b - k = 0 := Nat.sub_eq_zero_of_le hbk
  have hbk1 : b - (k + 1) = 0 := Nat.sub_eq_zero_of_le (by omega)
  have htake := accF_take_succ_of_le (W := W) (hbits := hbits) (b := b) (k := k) hbk
  have hdrop := accF_drop_succ_reverse_of_le (W := W) (hbits := hbits) (b := b) (k := k) hbk
  refine ⟨?_, ?_, ?_⟩
  · rw [htake, hO]; exact hOa
  · rw [hdrop, List.map_cons, h2, h2a]
    rfl
  · rw [hbk0] at hCWa
    rw [hbk1]
    exact hCW.trans hCWa

end Work.IntLib.evCA
