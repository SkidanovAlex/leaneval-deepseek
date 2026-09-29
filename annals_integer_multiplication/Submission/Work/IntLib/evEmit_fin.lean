import Mathlib
import Submission.Work.IntLib.evEmitDefs

/-!
# `IntLib` / `evEmit_fin`

The last phase of the `evEmit` word (`Submission/Work/IntLib/evEmitDefs.lean`): drain the region
above the marker of `evS2`, which is `(bits of V reversed) ++ [pos]`, onto stack 0 (already holding
`iend :: Y 0`).

Since `drainUntil` reverses the drained region, the resulting stack 0 is
`pos :: (bits of V) ++ iend :: Y 0 = Val.enc (.int V) ++ Y 0`, as required. The cost is linear in
the length of the drained region, i.e. in `V.size`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

theorem evEmit_fin (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (V : ℕ) (Y : HvdH.Stk → List HvdH.Glyph)
    (h0 : X 0 = HvdH.Glyph.iend :: Y 0)
    (hS2 : X Work.IntLib.evS2 = (V.bits.map HvdH.Glyph.bit).reverse ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk Work.IntLib.evS2 :: Y Work.IntLib.evS2) :
    ∃ (s' : HvdH.State) (n : ℕ),
      Work.Layout.Ev main (Work.IntLib.drainUntil Work.IntLib.evS2 0 (Work.IntLib.Shift.gmk Work.IntLib.evS2) Work.IntLib.evR) ⟨g, X⟩ s' n ∧
      n ≤ 5 * V.size + 11 ∧
      s'.stk 0 = HvdH.Val.enc (.int (V : ℤ)) ++ Y 0 ∧ s'.stk Work.IntLib.evS2 = Y Work.IntLib.evS2 ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.evS2 → s'.stk j = X j) := by
  set gs : List HvdH.Glyph := (V.bits.map HvdH.Glyph.bit).reverse ++ [HvdH.Glyph.pos] with hgs
  -- the region above the marker of `evS2`, in the form expected by `drainUntilEval`
  have hstk : X Work.IntLib.evS2 =
      gs ++ Work.IntLib.Shift.gmk Work.IntLib.evS2 :: Y Work.IntLib.evS2 := by
    rw [hgs, ← hS2]
  -- no glyph of the region is the marker
  have hne : ∀ h ∈ gs, h ≠ Work.IntLib.Shift.gmk Work.IntLib.evS2 := by
    intro h hh
    rw [hgs] at hh
    simp only [List.mem_append, List.mem_reverse, List.mem_map, List.mem_singleton] at hh
    rcases hh with ⟨b, -, rfl⟩ | rfl
    · exact Work.IntLib.Shift.bit_ne_gmk _ _
    · exact fun hc => Work.IntLib.Shift.gmk_ne_pos _ hc.symm
  obtain ⟨s', n, hn, hev, hk, hk', _hr, hoth⟩ :=
    drainUntilEval main Work.IntLib.evS2 0 (by decide) (Work.IntLib.Shift.gmk Work.IntLib.evS2)
      Work.IntLib.evR gs (Y Work.IntLib.evS2) ⟨g, X⟩ hne hstk
  -- cost: the region has length `V.size + 1`
  have hlen : gs.length = V.size + 1 := by
    rw [hgs, List.length_append, List.length_reverse, List.length_map, List.length_singleton,
      Nat.size_eq_bits_len]
  have hcost : n ≤ 5 * V.size + 11 := by omega
  -- `Val.enc (.int V)`
  have henc : HvdH.Val.enc (.int (V : ℤ)) =
      HvdH.Glyph.pos :: ((V.bits.map HvdH.Glyph.bit) ++ [HvdH.Glyph.iend]) := by
    rw [Work.IntLib.enc_int, Work.IntLib.encodeNat_eq_bits]
    have hnn : ¬ ((V : ℤ) < 0) := by omega
    rw [ite_eq_right hnn, Int.natAbs_natCast]
  -- the reversed region is exactly the sign followed by the bits of `V`
  have hrev : gs.reverse = HvdH.Glyph.pos :: V.bits.map HvdH.Glyph.bit := by
    rw [hgs, List.reverse_append, List.reverse_reverse, List.reverse_singleton,
      List.singleton_append]
  refine ⟨s', 5 * V.size + 11, ⟨n, hev, hcost⟩, le_rfl, ?_, hk, ?_⟩
  · rw [hk', hrev, henc]
    have hst0 : ({ reg := g, stk := X } : HvdH.State).stk 0 = HvdH.Glyph.iend :: Y 0 := h0
    rw [hst0]
    simp [List.append_assoc]
  · intro j hj0 hjS2
    exact hoth j hjS2 hj0

end Work.IntLib
