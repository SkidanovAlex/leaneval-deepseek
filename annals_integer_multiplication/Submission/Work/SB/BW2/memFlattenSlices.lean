import Mathlib
import Submission.Work.SB.BW2.Defs
import Submission.Work.SB.Core.slicesFlattenEq
import Submission.Work.Layout.sliceIdx

set_option autoImplicit false

/-!
# `memFlattenSlices`

Every entry of the flattened slice listing `(HvdH.slices A m B es).flatten` is an entry of `es`,
as soon as `es` really is a flat array of shape `A × m × B` (`es.length = A * m * B`).

The `Inhabited` default inside `HvdH.slices` is harmless in that case: every index it reads is
in range (`Work.Layout.invIdx1_lt`), so `es.getD i default = es[i]`.
-/

namespace Work.SB.BW2

open HvdH

theorem memFlattenSlices (A m B : ℕ) (es : List HvdH.Val) (hlen : es.length = A * m * B)
    {x : HvdH.Val} (hx : x ∈ (HvdH.slices A m B es).flatten) : x ∈ es := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: every slice is empty
    simp [HvdH.slices] at hx
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · -- `B = 0`: there are no slices at all
    simp [HvdH.slices] at hx
  · -- general case: the flattened listing reads consecutive in-range entries of `es`
    rw [Core.slicesFlattenEq A m B hm hB es hlen] at hx
    rw [List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hidx : Work.Layout.invIdx1 m B t < es.length := by
      rw [hlen]
      exact Work.Layout.invIdx1_lt A m B hm hB t (List.mem_range.mp ht)
    rw [List.getD_eq_getElem es _ hidx]
    exact List.getElem_mem hidx

end Work.SB.BW2
