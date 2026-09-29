import Mathlib
import Submission.Work.IntLib.evZeroDefs

namespace Work.IntLib

open HvdH
open Work.Layout

/-- Opening move of `zProg`: the two leading `pop`s (the chain tail `Glyph.nil` and the sign glyph
of `int b`) followed by the flag initialisation `zFl := zGo`.  Afterwards stack `0` holds exactly the
bits of `b` (least significant first) followed by the closing `iend` and the caller's `rest`, and the
loop flag is `zGo`.  Cost 3; every other stack is untouched. -/
theorem evZeroOpen (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (b : ℕ) (rest : List HvdH.Glyph)
    (hX : X 0 = [HvdH.Glyph.nil] ++ HvdH.Val.enc (.int (b : ℤ)) ++ rest) :
    ∃ (g' : HvdH.Reg → HvdH.Glyph) (Y : HvdH.Stk → List HvdH.Glyph),
      Work.Layout.Ev main
          (Work.Layout.seqs [HvdH.Cmd.pop Work.IntLib.zStk Work.IntLib.zFl,
                             HvdH.Cmd.pop Work.IntLib.zStk Work.IntLib.zFl,
                             HvdH.Cmd.set Work.IntLib.zFl Work.IntLib.zGo]) ⟨g, X⟩ ⟨g', Y⟩ 3 ∧
      g' Work.IntLib.zFl = Work.IntLib.zGo ∧
      Y Work.IntLib.zStk = (Computability.encodeNat b).map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: rest ∧
      (∀ j : HvdH.Stk, j ≠ 0 → Y j = X j) := by
  -- the encoding of `int b` (for `b : ℕ`) starts with the sign glyph `pos`
  have henc : HvdH.Val.enc (.int (b : ℤ)) =
      HvdH.Glyph.pos :: ((Computability.encodeNat b).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend]) := by
    simp [HvdH.Val.enc, Int.natAbs_natCast]
  -- hence after removing the two leading glyphs (`nil` and `pos`) the stack holds the bits, `iend`
  -- and the caller's tail
  have htail : (X Work.IntLib.zStk).tail.tail =
      (Computability.encodeNat b).map HvdH.Glyph.bit ++ HvdH.Glyph.iend :: rest := by
    have h0 : (X 0).tail.tail =
        ((Computability.encodeNat b).map HvdH.Glyph.bit ++ [HvdH.Glyph.iend]) ++ rest := by
      rw [hX, henc]
      rfl
    rw [show Work.IntLib.zStk = (0 : HvdH.Stk) from rfl, h0, List.append_assoc]
    rfl
  -- the three intermediate states, named so that the two `pop`s compose syntactically
  let g1 : HvdH.Reg → HvdH.Glyph := Function.update g Work.IntLib.zFl ((X Work.IntLib.zStk).headD .eos)
  let X1 : HvdH.Stk → List HvdH.Glyph := Function.update X Work.IntLib.zStk (X Work.IntLib.zStk).tail
  let g2 : HvdH.Reg → HvdH.Glyph := Function.update g1 Work.IntLib.zFl ((X1 Work.IntLib.zStk).headD .eos)
  let X2 : HvdH.Stk → List HvdH.Glyph := Function.update X1 Work.IntLib.zStk (X1 Work.IntLib.zStk).tail
  let g3 : HvdH.Reg → HvdH.Glyph := Function.update g2 Work.IntLib.zFl Work.IntLib.zGo
  have h1 : Work.Layout.Ev main (.pop Work.IntLib.zStk Work.IntLib.zFl) ⟨g, X⟩ ⟨g1, X1⟩ 1 :=
    Work.Layout.ev_pop' main Work.IntLib.zStk Work.IntLib.zFl g X
  have h2 : Work.Layout.Ev main (.pop Work.IntLib.zStk Work.IntLib.zFl) ⟨g1, X1⟩ ⟨g2, X2⟩ 1 :=
    Work.Layout.ev_pop' main Work.IntLib.zStk Work.IntLib.zFl g1 X1
  have h3 : Work.Layout.Ev main (.set Work.IntLib.zFl Work.IntLib.zGo) ⟨g2, X2⟩ ⟨g3, X2⟩ 1 :=
    Work.Layout.ev_set' main Work.IntLib.zFl Work.IntLib.zGo g2 X2
  refine ⟨g3, X2, ?_, ?_, ?_, ?_⟩
  · exact Work.Layout.Ev.seq h1 (Work.Layout.Ev.seq h2 h3)
  · simp [g3]
  · simp only [X2, X1, Function.update_self]
    exact htail
  · intro j hj
    simp only [X2, X1]
    rw [Function.update_of_ne (by simpa [Work.IntLib.zStk] using hj),
        Function.update_of_ne (by simpa [Work.IntLib.zStk] using hj)]

end Work.IntLib
