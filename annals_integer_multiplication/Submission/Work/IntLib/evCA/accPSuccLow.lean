import Mathlib
import Submission.Work.IntLib.evCarryDefs

/-!
# `IntLib` / `evCA`: one low step of the accumulation invariant

`Work.IntLib.EvC.accP b W hbits LO Os A2s Cs k s` records the accumulators of the ripple addition
after `k` steps: the first `min b k` produced sum bits sit, reversed (most significant on top), on
`aO` above `LO`, the remaining ones sit on `a2`, and the counter on `aCW` has lost `k` units.

This file proves that, while the counter is still positive (`k < b`, so the produced bit is a *low*
bit that has to go onto `aO`), pushing the `k`-th sum bit onto `aO` and popping one counter unit
does exactly take the invariant from `k` to `k + 1`.  It is the arithmetic half of the evaluation
lemma for the routing phase `EvC.routeA`; the evaluation itself is proved elsewhere.
-/

set_option autoImplicit false

namespace Work.IntLib.evCA

/-- One unfolding of the accumulator: the `(k+1)`-st sum bit is appended to the first `k`. -/
theorem accF_succL (W hbits : List Bool) (c : Bool) (k : ℕ) :
    Work.IntLib.EvC.accF W hbits c (k + 1) = Work.IntLib.EvC.accF W hbits c k ++
      [Work.IntLib.EvC.sumBit (W.getD k false) (hbits.getD k false)
        (Work.IntLib.EvC.carryC W hbits c k)] := rfl

/-- A unary counter with a positive number of units loses one unit and nothing else. -/
theorem Unary_tail_succL (n : ℕ) (rest : List HvdH.Glyph) :
    (Work.IntLib.Unary (n + 1) rest).tail = Work.IntLib.Unary n rest := by
  rw [Work.IntLib.Unary_succ]; rfl

/-- `accP` is preserved and advanced by one step when the produced sum bit is pushed onto `aO`
(the counter-positive case): the `k`-th sum bit moves from the pending part to the finalised low
bits, the high part is untouched and the counter loses one unit. -/
theorem accPSuccLow (b : ℕ) (W hbits LO : List Bool) (Os A2s Cs : List HvdH.Glyph)
    (k : ℕ) (s s' : HvdH.State) (hkb : k < b)
    (hacc : Work.IntLib.EvC.accP b W hbits LO Os A2s Cs k s)
    (hO : s'.stk Work.IntLib.aO = HvdH.Glyph.bit
        (Work.IntLib.EvC.sumBit (W.getD k false) (hbits.getD k false)
          (Work.IntLib.EvC.carryC W hbits false k)) :: s.stk Work.IntLib.aO)
    (h2 : s'.stk Work.IntLib.a2 = s.stk Work.IntLib.a2)
    (hCW : s'.stk Work.IntLib.aCW = (s.stk Work.IntLib.aCW).tail) :
    Work.IntLib.EvC.accP b W hbits LO Os A2s Cs (k + 1) s' := by
  obtain ⟨hO', h2', hCW'⟩ := hacc
  have hlt : (Work.IntLib.EvC.accF W hbits false k).length < b := by
    rw [Work.IntLib.EvC.accF_length]; exact hkb
  refine ⟨?_, ?_, ?_⟩
  · -- `aO`: the new sum bit lands on top of the finalised low bits.
    rw [hO, hO', accF_succL,
      Work.IntLib.EvC.take_append_singleton_of_lt _ _ hlt]
    simp
  · -- `a2`: the `(k+1)`-st bit is still below position `b`, so the high part is unchanged.
    rw [h2, h2', accF_succL,
      Work.IntLib.EvC.drop_append_singleton_of_lt _ _ hlt,
      List.drop_eq_nil_of_le (Nat.le_of_lt hlt)]
  · -- `aCW`: one counter unit was consumed, so `b - k` becomes `b - (k+1)`.
    rw [hCW, hCW']
    have hpos : 0 < b - k := Nat.sub_pos_of_lt hkb
    rw [show b - k = (b - k - 1) + 1 from (Nat.succ_pred_eq_of_pos hpos).symm,
      Unary_tail_succL, Nat.sub_sub]

end Work.IntLib.evCA
