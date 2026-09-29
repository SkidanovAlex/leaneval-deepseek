import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.paDefs
import Submission.Work.Compiler.stack_len_le

/-!
# Elementary helper facts for the `Ã` preamble (`Work.Resample.paStageD`)

Sizes of encodings, `Nat.size` bounds and the strict positivity of the cost of an `Eval`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The length of the encoding of a list of values is the sum of their `vsz`es. -/
theorem paLenEncS (vs : List Val) : (encs vs).length = (vs.map vsz).sum := by
  induction vs with
  | nil => simp [encs]
  | cons v vs ih =>
    rw [Work.Kernel.encs_cons, List.length_append, ih, List.map_cons, List.sum_cons]
    rfl

/-- `vsz` of an integer value at a natural number. -/
theorem paVszIntNat (n : ℕ) : vsz (Val.int (n : ℤ)) = n.size + 2 := by
  rw [Work.ConvR.vsz_int, isz, Int.natAbs_natCast]

/-- `n.size ≤ n`. -/
theorem paSizeLeSelf (n : ℕ) : n.size ≤ n := (Nat.size_le).mpr Nat.lt_two_pow_self

/-- `n.size ≤ k` iff `n < 2 ^ k`. -/
theorem paSizeLePow {n k : ℕ} : n.size ≤ k ↔ n < 2 ^ k := Nat.size_le

/-- Every `Eval` has cost at least `1`. -/
theorem paEvalPos {main c : Cmd} {s s' : State} {n : ℕ} (h : Eval main c s s' n) : 1 ≤ n := by
  induction h with
  | skip s => omega
  | pop k r s => omega
  | peek k r s => omega
  | push k r s => omega
  | set r c s => omega
  | mov dst src s => omega
  | seq h1 h2 ih1 ih2 => omega
  | iteT hr hsub ih => omega
  | iteF hr hsub ih => omega
  | loopF hr => omega
  | loopT hr hbody hloop ihbody ihloop => omega
  | self hsub ih => omega

end Work.Resample
