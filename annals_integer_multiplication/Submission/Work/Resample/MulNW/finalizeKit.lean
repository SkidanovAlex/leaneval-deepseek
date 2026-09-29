import Mathlib
import Submission.Work.Resample.MulNW.Defs
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.eval_stripZeros
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Kernel.Raw

/-!
# `Work.Resample.MulNW`: the finalisation phase

`finalizeProg` collects the running remainder and the accumulated output bits, strips the high zero
bits, computes the sign (here always `pos`) and writes the product back on stack 0.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Work.Resample.MulNW

open HvdH

/-! ## Helpers -/

theorem bitsG_ne_mk (l : List Bool) (i : Fin 16) (g : Glyph) (hg : g ∈ bitsG l) : g ≠ Glyph.mk i := by
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hg
  rw [← hb]
  exact bit_ne_mk b i

/-- `dropWhile` commutes with `map`. -/
theorem dropWhile_map_aux {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ (l : List α), (l.map f).dropWhile p = (l.dropWhile (fun a => p (f a))).map f
  | [] => rfl
  | a :: as => by
    rw [List.map_cons, List.dropWhile_cons, List.dropWhile_cons]
    by_cases h : p (f a) = true
    · rw [if_pos h, if_pos h]
      exact dropWhile_map_aux f p as
    · rw [if_neg h, if_neg h, List.map_cons]

/-- Stripping the high zero bits of the (most-significant-first) region `bitsG L.reverse` leaves
the canonical bit list of `ofBits L`, most significant first. -/
theorem bitsG_dropWhile (L : List Bool) :
    (bitsG L.reverse).dropWhile (fun g => g = Glyph.bit false) =
      bitsG ((Work.IntLib.ofBits L).bits.reverse) := by
  have h1 : L.reverse.dropWhile (fun b : Bool => !b) = ((Work.IntLib.ofBits L).bits).reverse := by
    rw [← Work.IntLib.MulS.stripHigh_eq_bits L, Work.IntLib.MulS.stripHigh, List.reverse_reverse]
  have h2 := dropWhile_map_aux (f := Glyph.bit) (p := fun g : Glyph => g = Glyph.bit false) L.reverse
  rw [h2]
  show (L.reverse.dropWhile (fun b : Bool => decide (Glyph.bit b = Glyph.bit false))).map Glyph.bit
      = ((Work.IntLib.ofBits L).bits.reverse).map Glyph.bit
  rw [show (fun b : Bool => decide (Glyph.bit b = Glyph.bit false)) = (fun b : Bool => !b) from by
      funext b; cases b <;> rfl,
    h1]

/-- `consume src T r (.push dst r)`: move the region of `src` above the marker `T` (reversed) onto
`dst`, restoring `src` down to `T`. -/
theorem drain_spec (main : Cmd) (src dst : Stk) (T : Glyph) (r : Reg) (l bk bk' : List Glyph)
    (s : State) (hne : src ≠ dst) (hT : ∀ g ∈ l, g ≠ T) (hsrc : s.stk src = l ++ T :: bk)
    (hdst : s.stk dst = bk') :
    ∃ s' n, Eval main (consume src T r (.push dst r)) s s' n ∧ n ≤ 5 * l.length + 8 ∧
      s'.stk src = T :: bk ∧ s'.stk dst = l.reverse ++ bk' ∧
      (∀ j : Stk, j ≠ src → j ≠ dst → s'.stk j = s.stk j) := by
  obtain ⟨s', n, e, hc, h1, h2, hf⟩ :=
    Work.IntLib.consume_push_rev main src T dst r l bk bk' hne hT s hsrc hdst
  exact ⟨s', n, e, hc, h1, h2, hf⟩

/-- `sgnProg` on two stored `pos` signs: the product is positive. -/
theorem sgnProg_spec (main : Cmd) (bkS : List Glyph) (s : State)
    (h : s.stk sS = Glyph.pos :: Glyph.pos :: mkS :: bkS) :
    ∃ s' n, Eval main sgnProg s s' n ∧ n ≤ 8 ∧ s'.stk sS = bkS ∧
      s'.reg rSign = Glyph.pos ∧ (∀ j : Stk, j ≠ sS → s'.stk j = s.stk j) := by
  let t1 : State := State.tPop s sS rBit
  let t2 : State := State.tPop t1 sS rA
  let t3 : State := State.tPop t2 sS rTmp
  have e1 : Eval main (.pop sS rBit) s t1 1 := Work.Kernel.eval_pop (main := main) sS rBit s
  have e2 : Eval main (.pop sS rA) t1 t2 1 := Work.Kernel.eval_pop (main := main) sS rA t1
  have e3 : Eval main (.pop sS rTmp) t2 t3 1 := Work.Kernel.eval_pop (main := main) sS rTmp t2
  have ht1S : t1.stk sS = Glyph.pos :: mkS :: bkS := by
    show Function.update s.stk sS (s.stk sS).tail sS = Glyph.pos :: mkS :: bkS
    rw [Function.update_self sS (s.stk sS).tail s.stk, h]
    simp
  have hr1 : t1.reg rBit = Glyph.pos := by
    show Function.update s.reg rBit ((s.stk sS).headD Glyph.eos) rBit = Glyph.pos
    rw [Function.update_self rBit ((s.stk sS).headD Glyph.eos) s.reg, h]
    simp
  have ht2S : t2.stk sS = mkS :: bkS := by
    show Function.update t1.stk sS (t1.stk sS).tail sS = mkS :: bkS
    rw [Function.update_self sS (t1.stk sS).tail t1.stk, ht1S]
    simp
  have hr2 : t2.reg rA = Glyph.pos := by
    show Function.update t1.reg rA ((t1.stk sS).headD Glyph.eos) rA = Glyph.pos
    rw [Function.update_self rA ((t1.stk sS).headD Glyph.eos) t1.reg, ht1S]
    simp
  have ht3S : t3.stk sS = bkS := by
    show Function.update t2.stk sS (t2.stk sS).tail sS = bkS
    rw [Function.update_self sS (t2.stk sS).tail t2.stk, ht2S]
    simp
  have hr3a : t3.reg rA = Glyph.pos := by
    show Function.update t2.reg rTmp ((t2.stk sS).headD Glyph.eos) rA = Glyph.pos
    rw [Function.update_of_ne (show rA ≠ rTmp by decide) ((t2.stk sS).headD Glyph.eos) t2.reg, hr2]
  have hr3b : t3.reg rBit = Glyph.pos := by
    show Function.update t2.reg rTmp ((t2.stk sS).headD Glyph.eos) rBit = Glyph.pos
    rw [Function.update_of_ne (show rBit ≠ rTmp by decide) ((t2.stk sS).headD Glyph.eos) t2.reg]
    show Function.update t1.reg rA ((t1.stk sS).headD Glyph.eos) rBit = Glyph.pos
    rw [Function.update_of_ne (show rBit ≠ rA by decide) ((t1.stk sS).headD Glyph.eos) t1.reg]
    show Function.update s.reg rBit ((s.stk sS).headD Glyph.eos) rBit = Glyph.pos
    rw [Function.update_self rBit ((s.stk sS).headD Glyph.eos) s.reg, h]
    simp
  have hneA : t3.reg rA ≠ Glyph.neg := by rw [hr3a]; decide
  have hneB : t3.reg rBit ≠ Glyph.neg := by rw [hr3b]; decide
  let t4 : State := State.tSet t3 rSign Glyph.pos
  have e4 : Eval main
      (.ite rA Glyph.neg (.ite rBit Glyph.neg (.set rSign Glyph.pos) (.set rSign Glyph.neg))
        (.ite rBit Glyph.neg (.set rSign Glyph.neg) (.set rSign Glyph.pos))) t3 t4 3 := by
    have hset : Eval main (.set rSign Glyph.pos) t3 t4 1 :=
      Work.Kernel.eval_set (main := main) rSign Glyph.pos t3
    have hinner : Eval main (.ite rBit Glyph.neg (.set rSign Glyph.neg) (.set rSign Glyph.pos))
        t3 t4 2 := Eval.iteF hneB hset
    exact Eval.iteF hneA hinner
  refine ⟨t4, 6, ?_, by omega, ?_, ?_, ?_⟩
  · have hh := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))
    simpa [sgnProg, Work.IntLib.MulS.seqs] using hh
  · show t3.stk sS = bkS
    exact ht3S
  · show (t3.updReg rSign Glyph.pos).reg rSign = Glyph.pos
    exact Function.update_self rSign Glyph.pos t3.reg
  · intro j hj
    show (t3.updReg rSign Glyph.pos).stk j = s.stk j
    rw [State.updReg_stk]
    show Function.update t2.stk sS (t2.stk sS).tail j = s.stk j
    rw [Function.update_of_ne hj (t2.stk sS).tail t2.stk]
    show Function.update t1.stk sS (t1.stk sS).tail j = s.stk j
    rw [Function.update_of_ne hj (t1.stk sS).tail t1.stk]
    show Function.update s.stk sS (s.stk sS).tail j = s.stk j
    rw [Function.update_of_ne hj (s.stk sS).tail s.stk]

end Work.Resample.MulNW
