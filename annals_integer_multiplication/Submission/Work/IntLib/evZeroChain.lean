import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.Base
import Submission.Work.IntLib.evZeroDefs
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.evZeroOpen
import Submission.Work.IntLib.evZeroLoop

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Layout

/-- Opening of the `evZeroChain` word: pop the leading `nil` of the chain, pop the sign glyph of
`int b`, and set the loop flag. -/
def zOpenP : Cmd := seqs [.pop zStk zFl, .pop zStk zFl, .set zFl zGo]

/-- Closing of the `evZeroChain` word: push `Glyph.iend` and then `Glyph.pos`, i.e. the encoding of
`int 0`. -/
def zCloseP : Cmd := seqs [.set zFl Glyph.iend, .push zStk zFl, .set zFl Glyph.pos, .push zStk zFl]

/-- The `evZeroChain` word: open, skip the encoding of `int b` (bits and closing `iend`), close. -/
def zWord : Cmd := seqs [zOpenP, zLoop, zCloseP]

/-- The closing part of the `evZeroChain` word: push `Glyph.iend` and then `Glyph.pos` back onto
stack `zStk`, i.e. replace the (already consumed) value by `Val.enc (.int 0) = [pos, iend]`. -/
theorem evZeroClose (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (Y : HvdH.Stk → List HvdH.Glyph)
    (rest : List HvdH.Glyph) (hY : Y zStk = rest) :
    ∃ g' : HvdH.Reg → HvdH.Glyph,
      Ev main (seqs [.set zFl Glyph.iend, .push zStk zFl, .set zFl Glyph.pos, .push zStk zFl])
        ⟨g, Y⟩ ⟨g', Function.update Y zStk (Glyph.pos :: Glyph.iend :: rest)⟩ 4 := by
  have h1 : Ev main (.set zFl Glyph.iend) ⟨g, Y⟩
      ⟨Function.update g zFl Glyph.iend, Y⟩ 1 := ev_set' main zFl Glyph.iend g Y
  have h2 : Ev main (.push zStk zFl) ⟨Function.update g zFl Glyph.iend, Y⟩
      ⟨Function.update g zFl Glyph.iend, Function.update Y zStk (Glyph.iend :: rest)⟩ 1 := by
    have h := ev_push' main zStk zFl (Function.update g zFl Glyph.iend) Y
    simpa [hY, Function.update_self] using h
  have h3 : Ev main (.set zFl Glyph.pos)
      ⟨Function.update g zFl Glyph.iend, Function.update Y zStk (Glyph.iend :: rest)⟩
      ⟨Function.update (Function.update g zFl Glyph.iend) zFl Glyph.pos,
        Function.update Y zStk (Glyph.iend :: rest)⟩ 1 :=
    ev_set' main zFl Glyph.pos _ _
  have h4 : Ev main (.push zStk zFl)
      ⟨Function.update (Function.update g zFl Glyph.iend) zFl Glyph.pos,
        Function.update Y zStk (Glyph.iend :: rest)⟩
      ⟨Function.update (Function.update g zFl Glyph.iend) zFl Glyph.pos,
        Function.update Y zStk (Glyph.pos :: Glyph.iend :: rest)⟩ 1 := by
    have h := ev_push' main zStk zFl
      (Function.update (Function.update g zFl Glyph.iend) zFl Glyph.pos)
      (Function.update Y zStk (Glyph.iend :: rest))
    simpa [Function.update_self, Function.update_idem] using h
  exact ⟨_, Ev.seqs_cons (cs := [.push zStk zFl, .set zFl Glyph.pos, .push zStk zFl]) h1
    (Ev.seqs_cons (cs := [.set zFl Glyph.pos, .push zStk zFl]) h2
      (Ev.seqs_cons (cs := [.push zStk zFl]) h3 h4))⟩

/-- The assembly: `evZeroOpen` (pop the leading `nil` and the sign, set the loop flag) followed by
`evZeroLoop` (skip the bits up to and including the closing `iend`) followed by `evZeroClose` (push
`iend`, `pos` back), i.e. the whole `evZeroChain` word, with cost `4 * b.size + 12 ≤ 8 * (b.size+4)`
and stack 0 replaced by `Val.enc (.int 0) ++ rest`, all other stacks untouched. -/
theorem evZeroMain
    (hOpen : ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
        (b : ℕ) (rest : List HvdH.Glyph),
        X 0 = [HvdH.Glyph.nil] ++ HvdH.Val.enc (.int (b : ℤ)) ++ rest →
        ∃ (g' : HvdH.Reg → HvdH.Glyph) (Y : HvdH.Stk → List HvdH.Glyph),
          Ev main (seqs [.pop zStk zFl, .pop zStk zFl, .set zFl zGo]) ⟨g, X⟩ ⟨g', Y⟩ 3 ∧
          g' zFl = zGo ∧
          Y zStk = (Computability.encodeNat b).map Glyph.bit ++ Glyph.iend :: rest ∧
          (∀ j : HvdH.Stk, j ≠ 0 → Y j = X j))
    (hLoop : ∀ (main : HvdH.Cmd) (bs : List Bool) (g : HvdH.Reg → HvdH.Glyph),
        g zFl = zGo →
        ∀ (Y : HvdH.Stk → List HvdH.Glyph) (rest : List HvdH.Glyph),
          Y zStk = bs.map Glyph.bit ++ Glyph.iend :: rest →
          ∃ g' : HvdH.Reg → HvdH.Glyph,
            Ev main zLoop ⟨g, Y⟩ ⟨g', Function.update Y zStk rest⟩ (4 * bs.length + 5)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph) (b : ℕ) (rest : List HvdH.Glyph),
      X 0 = [HvdH.Glyph.nil] ++ HvdH.Val.enc (.int (b : ℤ)) ++ rest →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧
        n ≤ K * (b.size + 4) ∧
        s'.stk 0 = HvdH.Val.enc (.int (0 : ℤ)) ++ rest ∧
        (∀ j : HvdH.Stk, j ≠ 0 → s'.stk j = X j) := by
  refine ⟨zWord, 8, ?_⟩
  intro main g X b rest hX
  obtain ⟨g1, Y1, hEv1, hg1, hY1, hfr1⟩ := hOpen main g X b rest hX
  obtain ⟨g2, hEv2⟩ := hLoop main (Computability.encodeNat b) g1 hg1 Y1 rest hY1
  obtain ⟨g3, hEv3⟩ :=
    evZeroClose main g2 (Function.update Y1 zStk rest) rest (Function.update_self zStk rest Y1)
  have hLen : (Computability.encodeNat b).length = b.size := encodeNat_length b
  refine ⟨⟨g3, Function.update Y1 zStk (Glyph.pos :: Glyph.iend :: rest)⟩,
    3 + ((4 * (Computability.encodeNat b).length + 5) + 4), ?_, ?_, ?_, ?_⟩
  · have h := Ev.seqs_cons (cs := [zLoop, zCloseP]) hEv1
      (Ev.seqs_cons (cs := [.set zFl Glyph.iend, .push zStk zFl, .set zFl Glyph.pos, .push zStk zFl])
        hEv2 hEv3)
    simpa [zWord, zOpenP, zCloseP, Function.update_idem] using h
  · omega
  · simp [zStk, Function.update_self, HvdH.Val.enc, Computability.encodeNat, Computability.encodeNum]
  · intro j hj
    have h1 : Function.update Y1 zStk (Glyph.pos :: Glyph.iend :: rest) j = Y1 j := by
      rw [zStk]
      exact Function.update_of_ne hj (Glyph.pos :: Glyph.iend :: rest) Y1
    exact h1.trans (hfr1 j hj)

theorem evZeroChain :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph) (b : ℕ) (rest : List HvdH.Glyph),
      X 0 = [HvdH.Glyph.nil] ++ HvdH.Val.enc (.int (b : ℤ)) ++ rest →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧
        n ≤ K * (b.size + 4) ∧
        s'.stk 0 = HvdH.Val.enc (.int (0 : ℤ)) ++ rest ∧
        (∀ j : HvdH.Stk, j ≠ 0 → s'.stk j = X j) :=
  evZeroMain evZeroOpen evZeroLoop

end Work.IntLib
