import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.MulNW.Defs
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.Resample.MulNW.addLoopCost

/-!
# `Work.Resample.MulNW.addA_ev`

The phase lemma for the inner addition phase `addAProg` of the schoolbook multiplication word:
starting with the bits of `α` on `sA`, the remainder `ρ` (same length) on `sR`, the bit `β` in
register `rBit` and the carry register `rCy` arbitrary, it adds `(β ? α : 0)` into `ρ` bit by bit,
pushes the low bit of the sum on `sC`, and leaves the halved remainder on `sR` (as
`(stepR α ρ β).2`).  Every other stack is restored, and the cost is `O(|α|)`.

The proof is a phase-by-phase state chase built on:
* `Work.Resample.MulNW.addLoopCost` — the addition loop over the bits of `α`;
* `Work.IntLib.consumeLoop_push_rev` — moving a marked region of a stack onto another stack.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.Resample.MulNW

open HvdH

/-! ## Toolkit: pointwise projections of `updStk`/`updReg` and list normal forms -/

private theorem updReg_reg_self {s : State} (r : Reg) (g : Glyph) : (s.updReg r g).reg r = g := by
  simp

private theorem updReg_reg_ne {s : State} {r r' : Reg} (h : r' ≠ r) (g : Glyph) :
    (s.updReg r g).reg r' = s.reg r' := by
  simp only [State.updReg_apply, if_neg h]

private theorem updReg_stk_eq {s : State} (r : Reg) (g : Glyph) (j : Stk) :
    (s.updReg r g).stk j = s.stk j := by
  simp only [State.updReg_stk]

private theorem updStk_stk_self {s : State} (k : Stk) (l : List Glyph) : (s.updStk k l).stk k = l := by
  simp

private theorem updStk_stk_ne {s : State} {k k' : Stk} (h : k' ≠ k) (l : List Glyph) :
    (s.updStk k l).stk k' = s.stk k' := by
  simp only [State.updStk_apply, if_neg h]

private theorem updStk_reg_eq {s : State} (k : Stk) (l : List Glyph) (r : Reg) :
    (s.updStk k l).reg r = s.reg r := rfl

/-- `bitsG l` is `l.map Glyph.bit`, exposed as a rewrite rule. -/
private theorem bitsG_map (l : List Bool) : bitsG l = l.map Glyph.bit := rfl

private theorem map_bitsG (l : List Bool) : l.map Glyph.bit = bitsG l := rfl

/-- `(a ++ [m]) ++ c` vs `a ++ m :: c`. -/
private theorem append_cons_form (a : List Glyph) (m : Glyph) (c : List Glyph) :
    a ++ [m] ++ c = a ++ m :: c := by
  simp only [List.append_assoc, List.singleton_append]

private theorem map_reverse_reverse (l : List Bool) :
    (l.reverse.map Glyph.bit).reverse = l.map Glyph.bit := by
  simp only [List.map_reverse, List.reverse_reverse]

private theorem headD_map_of_ne {α β : Type} {l : List α} (h : l ≠ []) (f : α → β) (d : β)
    (d' : α) : (l.map f).headD d = f (l.headD d') := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

private theorem headD_append_aux {α : Type} (l₁ l₂ : List α) (d : α) :
    (l₁ ++ l₂).headD d = l₁.headD (l₂.headD d) := by
  cases l₁ with
  | nil => rfl
  | cons x xs => rfl

private theorem tail_map_append_aux {α β : Type} (l : List α) (f : α → β) (rest : List β)
    (h : l ≠ []) : (l.map f ++ rest).tail = l.tail.map f ++ rest := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => rfl

private theorem bit_ne_mkT (c : Bool) : Glyph.bit c ≠ mkT := by intro hh; cases hh

private theorem bit_ne_mkW (c : Bool) : Glyph.bit c ≠ mkW := by intro hh; cases hh

/-! ## The phase lemma -/

theorem addA_ev (main : HvdH.Cmd) : Work.Resample.MulNW.AddASpec main := by
  intro α ρ β bkA bkR bkW bkT s hlen hA hR hW hT hbit
  -- ## Step 1: clear the carry register
  let s1 : State := s.updReg rCy (Glyph.bit false)
  have e1 : Eval main (.set rCy (Glyph.bit false)) s s1 1 := Eval.set rCy (Glyph.bit false) s
  have hs1cy : s1.reg rCy = Glyph.bit false := by
    simp only [s1, updReg_reg_self]
  have hs1bit : s1.reg rBit = Glyph.bit β := by
    simp only [s1, updReg_reg_ne (by decide : (rBit : Reg) ≠ rCy)]
    exact hbit
  -- (in the `[m] ++ below` form expected by the loop lemma)
  have hs1A : s1.stk sA = α.map Glyph.bit ++ [mkA] ++ bkA := by
    simp only [s1, updReg_stk_eq, hA, bitsG_map, List.append_assoc, List.singleton_append]
  have hs1R : s1.stk sR = ρ.map Glyph.bit ++ [mkR] ++ bkR := by
    simp only [s1, updReg_stk_eq, hR, bitsG_map, List.append_assoc, List.singleton_append]
  have hs1W : s1.stk sW = [mkW] ++ bkW := by
    simp only [s1, updReg_stk_eq]
    exact hW
  have hs1T : s1.stk sT = [mkT] ++ bkT := by
    simp only [s1, updReg_stk_eq]
    exact hT
  -- ## Step 2: the addition loop over the bits of `α`
  obtain ⟨s2, n2, e2, hn2, h2A, h2R, h2W, h2T, h2cy, h2fr⟩ :=
    addLoopCost main β false s1 α ρ [] [] bkA bkR bkW bkT hs1cy hs1bit hlen.symm
      hs1A hs1R hs1W hs1T
  have h2W' : s2.stk sW = bitsG α.reverse ++ mkW :: bkW := by
    simp only [h2W, bitsG_map, List.map_nil, List.append_nil, List.append_assoc,
      List.singleton_append]
  have h2T' : s2.stk sT
      = bitsG ((Work.IntLib.MulS.addBits (Work.IntLib.MulS.padFalse α β) ρ false).1.reverse)
        ++ mkT :: bkT := by
    simp only [h2T, bitsG_map, List.map_nil, List.append_nil, List.append_assoc,
      List.singleton_append]
  -- ## Step 3: push the carry-out bit on `sT`
  let sc : List Bool × Bool := Work.IntLib.MulS.addBits (Work.IntLib.MulS.padFalse α β) ρ false
  let L : List Bool := sc.1 ++ [sc.2]
  let ws : List Glyph := Glyph.bit sc.2 :: sc.1.reverse.map Glyph.bit
  have hLne : L ≠ [] := by
    intro hc
    have h' : [sc.2] = ([] : List Bool) := (List.append_eq_nil_iff.mp hc).2
    exact (List.cons_ne_nil sc.2 ([] : List Bool)) h'
  let s3 : State := s2.updStk sT (s2.reg rCy :: s2.stk sT)
  have e3 : Eval main (.push sT rCy) s2 s3 1 := Eval.push sT rCy s2
  have h3T : s3.stk sT = ws ++ mkT :: bkT := by
    simp only [s3, updStk_stk_self, h2cy, h2T', ws, sc, bitsG_map, List.cons_append]
  have h3R : s3.stk sR = mkR :: bkR := by
    simp only [s3, updStk_stk_ne (by decide : (sR : Stk) ≠ sT), h2R, List.singleton_append]
  have h3A : s3.stk sA = mkA :: bkA := by
    simp only [s3, updStk_stk_ne (by decide : (sA : Stk) ≠ sT), h2A, List.singleton_append]
  have h3W : s3.stk sW = bitsG α.reverse ++ mkW :: bkW := by
    simp only [s3, updStk_stk_ne (by decide : (sW : Stk) ≠ sT), h2W']
  have h3C : s3.stk sC = s.stk sC := by
    have h32 : s3.stk sC = s2.stk sC := by
      simp only [s3, updStk_stk_ne (by decide : (sC : Stk) ≠ sT)]
    have h21 : s2.stk sC = s1.stk sC := h2fr sC (by decide) (by decide) (by decide) (by decide)
    have h10 : s1.stk sC = s.stk sC := by
      simp only [s1, updReg_stk_eq]
    rw [h32, h21, h10]
  -- ## Step 4: drain the bits on `sT` onto `sR`
  let s3' : State := s3.updReg rL Glyph.eos
  have e3' : Eval main (.set rL Glyph.eos) s3 s3' 1 := Eval.set rL Glyph.eos s3
  have h3'T : s3'.stk sT = ws ++ mkT :: bkT := by
    simp only [s3', updReg_stk_eq, h3T]
  have h3'R : s3'.stk sR = mkR :: bkR := by
    simp only [s3', updReg_stk_eq, h3R]
  have h3'rL : s3'.reg rL = Glyph.eos := by
    simp only [s3', updReg_reg_self]
  have h3ws : ∀ g ∈ ws, g ≠ mkT := by
    intro g hg
    simp only [ws, List.mem_cons] at hg
    rcases hg with hg | hg
    · rw [hg]; exact bit_ne_mkT sc.2
    · exact bitsG_ne_mkA sc.1.reverse g hg 6
  obtain ⟨s4, n4, e4, h4T, h4R, -, hn4, h4fr⟩ :=
    Work.IntLib.consumeLoop_push_rev main sT mkT sR rL (by decide) bkT (mkR :: bkR) ws h3ws
      [] ws s3' rfl h3'T h3'R h3'rL
  have h4rev : ws.reverse = L.map Glyph.bit := by
    simp only [ws, L, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.map_reverse, List.reverse_reverse]
  have h4R' : s4.stk sR = bitsG L ++ mkR :: bkR := by
    rw [h4R, h4rev, map_bitsG]
  have h3'A : s3'.stk sA = mkA :: bkA := by
    simp only [s3', updReg_stk_eq, h3A]
  have h3'W : s3'.stk sW = bitsG α.reverse ++ mkW :: bkW := by
    simp only [s3', updReg_stk_eq, h3W]
  have h3'C : s3'.stk sC = s.stk sC := by
    simp only [s3', updReg_stk_eq, h3C]
  have h4A : s4.stk sA = mkA :: bkA := (h4fr sA (by decide) (by decide)).trans h3'A
  have h4W : s4.stk sW = bitsG α.reverse ++ mkW :: bkW :=
    (h4fr sW (by decide) (by decide)).trans h3'W
  have h4C : s4.stk sC = s.stk sC := (h4fr sC (by decide) (by decide)).trans h3'C
  -- ## Step 5: drain the bits on `sW` back onto `sA`
  let s4' : State := s4.updReg rL Glyph.eos
  have e4' : Eval main (.set rL Glyph.eos) s4 s4' 1 := Eval.set rL Glyph.eos s4
  have h4'W : s4'.stk sW = α.reverse.map Glyph.bit ++ mkW :: bkW := by
    simp only [s4', updReg_stk_eq, h4W, bitsG_map]
  have h4'A : s4'.stk sA = mkA :: bkA := by
    simp only [s4', updReg_stk_eq, h4A]
  have h4'T : s4'.stk sT = mkT :: bkT := by
    simp only [s4', updReg_stk_eq, h4T]
  have h4'rL : s4'.reg rL = Glyph.eos := by
    simp only [s4', updReg_reg_self]
  have h4ws : ∀ g ∈ α.reverse.map Glyph.bit, g ≠ mkW :=
    fun g hg => bitsG_ne_mkA α.reverse g hg 7
  obtain ⟨s5, n5, e5, h5W, h5A, -, hn5, h5fr⟩ :=
    Work.IntLib.consumeLoop_push_rev main sW mkW sA rL (by decide) bkW (mkA :: bkA)
      (α.reverse.map Glyph.bit) h4ws [] (α.reverse.map Glyph.bit) s4' rfl h4'W h4'A h4'rL
  have h5A' : s5.stk sA = bitsG α ++ mkA :: bkA := by
    rw [h5A, map_reverse_reverse, map_bitsG]
  have h5R : s5.stk sR = bitsG L ++ mkR :: bkR := by
    have h4'R : s4'.stk sR = bitsG L ++ mkR :: bkR := by
      simp only [s4', updReg_stk_eq, h4R']
    rw [h5fr sR (by decide) (by decide), h4'R]
  have h5T : s5.stk sT = mkT :: bkT := by
    rw [h5fr sT (by decide) (by decide), h4'T]
  have h5C : s5.stk sC = s.stk sC := by
    have h4'C : s4'.stk sC = s.stk sC := by
      simp only [s4', updReg_stk_eq, h4C]
    rw [h5fr sC (by decide) (by decide), h4'C]
  -- ## Step 6: pop the low bit of `sR` into `rOut`
  let s6 : State := (s5.updStk sR (s5.stk sR).tail).updReg rOut ((s5.stk sR).headD Glyph.eos)
  have e6 : Eval main (.pop sR rOut) s5 s6 1 := Eval.pop sR rOut s5
  have h6out : s6.reg rOut = Glyph.bit (L.headD false) := by
    have hreg : s6.reg rOut = (s5.stk sR).headD Glyph.eos := by
      simp only [s6, updReg_reg_self]
    rw [hreg, h5R, bitsG_map, headD_append_aux, headD_map_of_ne hLne Glyph.bit _ false]
  have h6R : s6.stk sR = bitsG L.tail ++ mkR :: bkR := by
    have hstk : s6.stk sR = (s5.stk sR).tail := by
      simp only [s6, updStk_stk_self, updReg_stk_eq]
    rw [hstk, h5R, bitsG_map, tail_map_append_aux L Glyph.bit (mkR :: bkR) hLne, map_bitsG]
  have h6C : s6.stk sC = s.stk sC := by
    have h1 : s6.stk sC = s5.stk sC := by
      simp only [s6, updStk_stk_ne (by decide : (sC : Stk) ≠ sR), updReg_stk_eq]
    rw [h1, h5C]
  -- ## Step 7: push the output bit on `sC`
  let s7 : State := s6.updStk sC (s6.reg rOut :: s6.stk sC)
  have e7 : Eval main (.push sC rOut) s6 s7 1 := Eval.push sC rOut s6
  have h7C : s7.stk sC = Glyph.bit (L.headD false) :: s.stk sC := by
    have hstk : s7.stk sC = s6.reg rOut :: s6.stk sC := by
      simp only [s7, updStk_stk_self]
    rw [hstk, h6out, h6C]
  -- ## Transfer lemmas
  have h76 : ∀ j : Stk, j ≠ sC → s7.stk j = s6.stk j := by
    intro j hj
    simp only [s7, updStk_stk_ne hj]
  have h65 : ∀ j : Stk, j ≠ sR → s6.stk j = s5.stk j := by
    intro j hj
    simp only [s6, updStk_stk_ne hj, updReg_stk_eq]
  have frame6 : ∀ j : Stk, j ≠ sA → j ≠ sR → j ≠ sT → j ≠ sW → s6.stk j = s.stk j := by
    intro j hjA hjR hjT hjW
    have h54 : s5.stk j = s4'.stk j := h5fr j hjW hjA
    have h4'4 : s4'.stk j = s4.stk j := by simp only [s4', updReg_stk_eq]
    have h4'3 : s4'.stk j = s3'.stk j := h4fr j hjT hjR
    have h3'3 : s3'.stk j = s3.stk j := by simp only [s3', updReg_stk_eq]
    have h32 : s3.stk j = s2.stk j := by simp only [s3, updStk_stk_ne hjT]
    have h21 : s2.stk j = s1.stk j := h2fr j hjA hjR hjW hjT
    have h10 : s1.stk j = s.stk j := by simp only [s1, updReg_stk_eq]
    calc s6.stk j = s5.stk j := h65 j hjR
      _ = s4'.stk j := h54
      _ = s4.stk j := h4'4
      _ = s3'.stk j := h4'3
      _ = s3.stk j := h3'3
      _ = s2.stk j := h32
      _ = s1.stk j := h21
      _ = s.stk j := h10
  -- ## The final stack contents
  have hAfin : s7.stk sA = bitsG α ++ mkA :: bkA :=
    ((h76 sA (by decide)).trans (h65 sA (by decide))).trans h5A'
  have hRfin : s7.stk sR = bitsG L.tail ++ mkR :: bkR := (h76 sR (by decide)).trans h6R
  have hWfin : s7.stk sW = mkW :: bkW :=
    ((h76 sW (by decide)).trans (h65 sW (by decide))).trans h5W
  have hTfin : s7.stk sT = mkT :: bkT :=
    (((h76 sT (by decide)).trans (h65 sT (by decide))).trans
      (h5fr sT (by decide) (by decide))).trans h4'T
  -- ## The arithmetic relation to `stepR`
  have hsR1 : (Work.IntLib.MulS.stepR α ρ β).1 = L.headD false := by
    dsimp only [Work.IntLib.MulS.stepR]
  have hsR2 : (Work.IntLib.MulS.stepR α ρ β).2 = L.tail := by
    dsimp only [Work.IntLib.MulS.stepR]
  -- ## The cost
  have hsc1len : sc.1.length = α.length := by
    simp only [sc, Work.IntLib.MulS.addBits_len (Work.IntLib.MulS.padFalse α β) ρ
      (by rw [Work.IntLib.MulS.padFalse_length, hlen.symm]) false,
      Work.IntLib.MulS.padFalse_length]
  have hws_len : ws.length = α.length + 1 := by
    simp only [ws, List.length_cons, List.length_map, List.length_reverse, hsc1len]
  have hrevlen : (α.reverse.map Glyph.bit).length = α.length := by
    simp only [List.length_map, List.length_reverse]
  let C : ℕ := 1 + (n2 + (1 + ((1 + n4) + ((1 + n5) + (1 + 1)))))
  have hcost : C ≤ 30 * (α.length + 2) := by
    have h4b := hn4
    rw [hws_len] at h4b
    have h5b := hn5
    rw [hrevlen] at h5b
    dsimp only [C]
    omega
  -- ## The run
  have hdT : Eval main (Work.IntLib.consume sT mkT rL (.push sR rL)) s3 s4 (1 + n4) :=
    Eval.seq e3' e4
  have hdW : Eval main (Work.IntLib.consume sW mkW rL (.push sA rL)) s4 s5 (1 + n5) :=
    Eval.seq e4' e5
  have h67 : Eval main (.seq (.pop sR rOut) (.push sC rOut)) s5 s7 (1 + 1) := Eval.seq e6 e7
  have hW67 : Eval main
      (.seq (Work.IntLib.consume sW mkW rL (.push sA rL))
        (.seq (.pop sR rOut) (.push sC rOut))) s4 s7 ((1 + n5) + (1 + 1)) :=
    Eval.seq hdW h67
  have hT67 : Eval main
      (.seq (Work.IntLib.consume sT mkT rL (.push sR rL))
        (.seq (Work.IntLib.consume sW mkW rL (.push sA rL))
          (.seq (.pop sR rOut) (.push sC rOut)))) s3 s7
      ((1 + n4) + ((1 + n5) + (1 + 1))) :=
    Eval.seq hdT hW67
  have hpush67 : Eval main
      (.seq (.push sT rCy)
        (.seq (Work.IntLib.consume sT mkT rL (.push sR rL))
          (.seq (Work.IntLib.consume sW mkW rL (.push sA rL))
            (.seq (.pop sR rOut) (.push sC rOut))))) s2 s7
      (1 + ((1 + n4) + ((1 + n5) + (1 + 1)))) :=
    Eval.seq e3 hT67
  have hloop67 : Eval main
      (.seq (Work.IntLib.consume sA mkA rL addABody)
        (.seq (.push sT rCy)
          (.seq (Work.IntLib.consume sT mkT rL (.push sR rL))
            (.seq (Work.IntLib.consume sW mkW rL (.push sA rL))
              (.seq (.pop sR rOut) (.push sC rOut)))))) s1 s7
      (n2 + (1 + ((1 + n4) + ((1 + n5) + (1 + 1))))) :=
    Eval.seq e2 hpush67
  have hall : Eval main Work.Resample.MulNW.addAProg s s7 C := Eval.seq e1 hloop67
  -- ## Assemble
  refine ⟨s7, C, hall, hcost, hAfin, ?_, ?_, hWfin, hTfin, ?_⟩
  · rw [hsR2]
    exact hRfin
  · rw [hsR1]
    exact h7C
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨h1, h2, h3, h4, h5⟩ := hj
    rw [h76 j h2]
    exact frame6 j h1 h3 h4 h5

end Work.Resample.MulNW
