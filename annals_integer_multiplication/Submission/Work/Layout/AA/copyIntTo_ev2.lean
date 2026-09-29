import Mathlib
import Submission.Work.Layout.AA.ProgAux
import Submission.Work.Layout.AA.Defs
import Submission.Work.Layout.AA.copyIntB1_loop
import Submission.Work.Layout.AA.enc_int_decomp
import Submission.Work.Layout.AA.copyIntB2_loop

/-!
# `copyIntTo`: no hypothesis on the content below the marker

`Work.Layout.copyIntTo a b t rr rf` copies the integer value on top of `a` onto `b`, keeping it on
`a`; `t` is scratch and carries the boundary marker `gMark = Glyph.mk 7` with arbitrary content
`DB` underneath it.

This is the version of the specification of `Work.Layout.LayoutLib.copyIntTo` that needs **no**
hypothesis on `DB`: the second phase of the program peeks the top of `t` and stops at the first
marker, and the glyphs it walks over before that (the encoding `(Val.int k).enc`, which is
marker-free) are precisely the ones copied -- what lies below the marker is never inspected.

The proof is the same as that of `Submission.Work.Layout.AA.copyIntTo_ev`; the sole difference is
that the marker-freeness hypothesis on `DB` (which the proof there never uses) is dropped, so the
phase-2 loop lemma is taken from `Submission.Work.Layout.AA.copyIntB2_loop`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Layout.AA

open HvdH

theorem copyIntTo_ev2 (main : HvdH.Cmd) (a b t : HvdH.Stk) (rr rf : HvdH.Reg) (hrt : rr ≠ rf)
    (hat : a ≠ t) (hbt : b ≠ t) (hab : a ≠ b)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (k : ℕ)
    (A B DB : List HvdH.Glyph)
    (ha : X a = (HvdH.Val.int (k : ℤ)).enc ++ A) (hb : X b = B)
    (ht : X t = Work.Layout.gMark :: DB) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.copyIntTo a b t rr rf) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (HvdH.isz k + 1) ∧
      s'.stk a = (HvdH.Val.int (k : ℤ)).enc ++ A ∧ s'.stk b = (HvdH.Val.int (k : ℤ)).enc ++ B ∧
      s'.stk t = Work.Layout.gMark :: DB ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ t → s'.stk j = X j) := by
  -- the digits of the encoding of `k` (sign glyph plus the bits, least significant first)
  obtain ⟨D, hE, hDiend, hDmk, hDlen⟩ := enc_int_decomp k
  have ha' : X a = D ++ Glyph.iend :: A := by rw [ha, hE]; simp
  -- the marker `gMark` is the glyph `Glyph.mk 7`
  have hgm : X t = Glyph.mk 7 :: DB := ht
  -- phase 1: move `(Val.int k).enc` from `a` onto `t` (reversed)
  have hg1 : (Function.update g rf Glyph.cons) rf = Glyph.cons := by simp
  obtain ⟨s1, hrun1, ha1, ht1, hfr1, hr1⟩ :=
    copyIntB1_loop main (hat := hat) (rr := rr) (rf := rf) D A
      (Function.update g rf Glyph.cons) X hDiend hg1 ha'
  have hloop1 : Ev main (.loop rf Glyph.cons (copyIntB1 a t rr rf))
      ⟨Function.update g rf Glyph.cons, X⟩ s1 (5 * (D.length + 1) + 1) :=
    loopRuns.eval hrun1 (by rw [hr1]; decide)
  -- the block moved onto `t` carries no marker, so the second loop stops exactly at the boundary
  have hDmk' : Glyph.mk 7 ∉ (Glyph.iend :: D.reverse) := by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    · exact hDmk (List.mem_reverse.mp h)
  have ht1' : s1.stk t = (Glyph.iend :: D.reverse) ++ Glyph.mk 7 :: DB := by
    rw [ht1, hgm]
  -- phase 2: walk `t` back down to the marker, restoring the glyphs on `a` and copying them to `b`
  obtain ⟨s2, hrun2, ht2, ha2, hb2, hfr2, hr2⟩ :=
    copyIntB2_loop main (hta := Ne.symm hat) (htb := Ne.symm hbt) (hab := hab)
      (rr := rr) (rf := rf) (Glyph.iend :: D.reverse) DB
      (Function.update s1.reg rf Glyph.cons) s1.stk hDmk' (by simp) ht1'
  have hloop2 : Ev main (.loop rf Glyph.cons (copyIntB2 t a b rr rf))
      ⟨Function.update s1.reg rf Glyph.cons, s1.stk⟩ s2
      (7 * ((Glyph.iend :: D.reverse).length + 1) + 1) :=
    loopRuns.eval hrun2 (by rw [hr2]; decide)
  have hset1 : Ev main (.set rf Glyph.cons) ⟨g, X⟩ ⟨Function.update g rf Glyph.cons, X⟩ 1 :=
    ev_set main rf Glyph.cons ⟨g, X⟩
  have hset2 : Ev main (.set rf Glyph.cons) s1 ⟨Function.update s1.reg rf Glyph.cons, s1.stk⟩ 1 :=
    ev_set main rf Glyph.cons s1
  have hprog : copyIntTo a b t rr rf = .seq (.set rf Glyph.cons)
      (.seq (.loop rf Glyph.cons (copyIntB1 a t rr rf))
        (.seq (.set rf Glyph.cons) (.loop rf Glyph.cons (copyIntB2 t a b rr rf)))) := rfl
  -- cost: 1 + (5(m+1) + 1) + (1 + 7(m+2) + 1) = 12·isz k + 11 ≤ 16·(isz k + 1)
  have hcost : 1 + ((5 * (D.length + 1) + 1) +
      (1 + (7 * ((Glyph.iend :: D.reverse).length + 1) + 1))) ≤ 16 * (isz (k : ℤ) + 1) := by
    have hlen : (Glyph.iend :: D.reverse).length = D.length + 1 := by simp
    rw [hlen, hDlen]; omega
  have hEv : Ev main (copyIntTo a b t rr rf) ⟨g, X⟩ s2 (16 * (isz (k : ℤ) + 1)) := by
    rw [hprog]
    exact (Ev.seq hset1 (Ev.seq hloop1 (Ev.seq hset2 hloop2))).mono hcost
  have hrev : (Glyph.iend :: D.reverse).reverse = (Val.int (k : ℤ)).enc := by
    rw [List.reverse_cons, List.reverse_reverse]
    rw [hE]
  have hsb : s1.stk b = B := by rw [hfr1 b hab.symm hbt, hb]
  refine ⟨s2, 16 * (isz (k : ℤ) + 1), hEv, le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [ha2, ha1, hrev]
  · rw [hb2, hsb, hrev]
  · show s2.stk t = Glyph.mk 7 :: DB
    exact ht2
  · intro j hja hjb hjt
    rw [hfr2 j hjt hja hjb, hfr1 j hja hjt]

end Work.Layout.AA
