import Mathlib
import Submission.Work.SynFFT.axisLeafDefs
import Submission.Work.Layout.AA.ProgAux
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

/-!
# `Work.SynFFT.leafElemStepEv`

One iteration of the element loop of the leaf word of the blockwise transpose (`axisLeafDefs`).

Starting from `ofList L` on `lfStBk` and `cons :: (v.enc ++ rest)` on `lfStF`, the word
`lfElemStep` pops the `cons`, moves `v` aside, pushes a `nil` (the tail of the singleton column),
moves `v` above it and closes the singleton with two `cons` glyphs.  The net effect is that `v` is
pushed onto the row list `L` as the singleton column `ofList [v] = cons v nil`, at the cost of a
constant number of `mvVal` moves (i.e. `≤ 60 * (vsz v + 1)` steps).

The scratch stacks `lfStM1`, `lfCA`, `lfCB` are fully restored.
-/

namespace Work.SynFFT

open HvdH
open Work.Layout

/-- `lfElemStep`, spelled out as its list of six commands. -/
theorem lfElemStep_unfold :
    lfElemStep = seqs [HvdH.Cmd.pop lfStF lfP, mvVal lfStF lfStM1 lfCA lfCB,
      Work.Kernel.pushGlyphs [HvdH.Glyph.nil] lfStBk lfQ,
      mvVal lfStM1 lfStBk lfCA lfCB,
      Work.Kernel.pushGlyphs [HvdH.Glyph.cons] lfStBk lfQ,
      Work.Kernel.pushGlyphs [HvdH.Glyph.cons] lfStBk lfQ] := rfl

/-- The encoding of `ofList [v] :: L`, in the shape produced by `lfElemStep`. -/
theorem ofList_singleton_cons_enc (v : HvdH.Val) (L : List HvdH.Val) (G : List HvdH.Glyph) :
    (HvdH.ofList (HvdH.ofList [v] :: L)).enc ++ G =
      HvdH.Glyph.cons ::
        (HvdH.Glyph.cons :: (v.enc ++ (HvdH.Glyph.nil :: ((HvdH.ofList L).enc ++ G)))) := by
  simp [HvdH.ofList, HvdH.Val.enc, List.append_assoc]

set_option maxHeartbeats 1000000 in
theorem leafElemStepEv (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
    (X : HvdH.Stk → List HvdH.Glyph) (v : HvdH.Val) (rest : List HvdH.Glyph)
    (L : List HvdH.Val) (G : List HvdH.Glyph)
    (ha : X Work.SynFFT.lfStF = HvdH.Glyph.cons :: (v.enc ++ rest))
    (hb : X Work.SynFFT.lfStBk = (HvdH.ofList L).enc ++ G) :
    ∃ s' n, Work.Layout.Ev main Work.SynFFT.lfElemStep ⟨g, X⟩ s' n ∧
      n ≤ 60 * (HvdH.vsz v + 1) ∧ s'.stk Work.SynFFT.lfStF = rest ∧
      s'.stk Work.SynFFT.lfStBk = (HvdH.ofList (HvdH.ofList [v] :: L)).enc ++ G ∧
      (∀ j, j ≠ Work.SynFFT.lfStF → j ≠ Work.SynFFT.lfStBk → s'.stk j = X j) := by
  have hFM : lfStF ≠ lfStM1 := by decide
  have hFB : lfStF ≠ lfStBk := by decide
  have hFC : lfStF ≠ lfCA := by decide
  have hFD : lfStF ≠ lfCB := by decide
  have hMB : lfStM1 ≠ lfStBk := by decide
  have hMC : lfStM1 ≠ lfCA := by decide
  have hMD : lfStM1 ≠ lfCB := by decide
  have hBC : lfStBk ≠ lfCA := by decide
  have hBD : lfStBk ≠ lfCB := by decide
  have hCD : lfCA ≠ lfCB := by decide
  -- the state after the initial `pop`
  let g1 : HvdH.Reg → HvdH.Glyph := Function.update g lfP HvdH.Glyph.cons
  let X0 : HvdH.Stk → List HvdH.Glyph := Function.update X lfStF (v.enc ++ rest)
  have hX0F : X0 lfStF = v.enc ++ rest := by
    show Function.update X lfStF (v.enc ++ rest) lfStF = v.enc ++ rest
    exact Function.update_self lfStF (v.enc ++ rest) X
  have hX0M : X0 lfStM1 = X lfStM1 := by
    show Function.update X lfStF (v.enc ++ rest) lfStM1 = X lfStM1
    exact Function.update_of_ne hFM.symm (v.enc ++ rest) X
  have hX0B : X0 lfStBk = X lfStBk := by
    show Function.update X lfStF (v.enc ++ rest) lfStBk = X lfStBk
    exact Function.update_of_ne hFB.symm (v.enc ++ rest) X
  have hX0C : X0 lfCA = X lfCA := by
    show Function.update X lfStF (v.enc ++ rest) lfCA = X lfCA
    exact Function.update_of_ne hFC.symm (v.enc ++ rest) X
  have hX0D : X0 lfCB = X lfCB := by
    show Function.update X lfStF (v.enc ++ rest) lfCB = X lfCB
    exact Function.update_of_ne hFD.symm (v.enc ++ rest) X
  -- (1) pop the leading `cons`
  have hpop : Ev main (HvdH.Cmd.pop lfStF lfP) ⟨g, X⟩ ⟨g1, X0⟩ 1 := by
    have h := ev_pop' main lfStF lfP g X
    have hhd : (X lfStF).headD HvdH.Glyph.eos = HvdH.Glyph.cons := by simp [ha]
    have htl : (X lfStF).tail = v.enc ++ rest := by simp [ha]
    rw [hhd, htl] at h
    exact h
  -- (2) move `v` from `lfStF` to the scratch stack `lfStM1`
  obtain ⟨s2, n2, he2, hn2, h2F, h2M, h2CA, h2CB, h2fr⟩ :=
    mvVal_ev_full (main := main) (a := lfStF) (b := lfStM1) (c := lfCA) (d := lfCB)
      hFM hFC hFD hMC hMD hCD (g := g1) (X := X0) (v := v) (A := rest) (B := X0 lfStM1)
      hX0F rfl
  have he2' : Ev main (mvVal lfStF lfStM1 lfCA lfCB) ⟨g1, X0⟩ ⟨s2.reg, s2.stk⟩ n2 := he2
  -- (3) push the `nil` tail of the singleton column on `lfStBk`
  obtain ⟨s3, n3, he3, hn3, h3Bk, h3fr⟩ :=
    Work.Layout.AA.pushGlyphs_ev main [HvdH.Glyph.nil] lfStBk lfQ s2.reg s2.stk
  have he3' : Ev main (Work.Kernel.pushGlyphs [HvdH.Glyph.nil] lfStBk lfQ)
      ⟨s2.reg, s2.stk⟩ ⟨s3.reg, s3.stk⟩ n3 := he3
  have hn3' : n3 ≤ 3 := le_trans hn3 (by decide)
  -- (4) move `v` above that `nil`
  have h4a : s3.stk lfStM1 = v.enc ++ X0 lfStM1 := by rw [h3fr lfStM1 hMB, h2M]
  obtain ⟨s4, n4, he4, hn4, h4M, h4Bk, h4CA, h4CB, h4fr⟩ :=
    mvVal_ev_full (main := main) (a := lfStM1) (b := lfStBk) (c := lfCA) (d := lfCB)
      hMB hMC hMD hBC hBD hCD (g := s3.reg) (X := s3.stk) (v := v)
      (A := X0 lfStM1) (B := s3.stk lfStBk) h4a rfl
  have he4' : Ev main (mvVal lfStM1 lfStBk lfCA lfCB) ⟨s3.reg, s3.stk⟩ ⟨s4.reg, s4.stk⟩ n4 :=
    he4
  -- (5) close the singleton column with two `cons` glyphs
  obtain ⟨s5, n5, he5, hn5, h5Bk, h5fr⟩ :=
    Work.Layout.AA.pushGlyphs_ev main [HvdH.Glyph.cons] lfStBk lfQ s4.reg s4.stk
  have he5' : Ev main (Work.Kernel.pushGlyphs [HvdH.Glyph.cons] lfStBk lfQ)
      ⟨s4.reg, s4.stk⟩ ⟨s5.reg, s5.stk⟩ n5 := he5
  have hn5' : n5 ≤ 3 := le_trans hn5 (by decide)
  obtain ⟨s6, n6, he6, hn6, h6Bk, h6fr⟩ :=
    Work.Layout.AA.pushGlyphs_ev main [HvdH.Glyph.cons] lfStBk lfQ s5.reg s5.stk
  have he6' : Ev main (Work.Kernel.pushGlyphs [HvdH.Glyph.cons] lfStBk lfQ)
      ⟨s5.reg, s5.stk⟩ ⟨s6.reg, s6.stk⟩ n6 := he6
  have hn6' : n6 ≤ 3 := le_trans hn6 (by decide)
  -- the cost of the whole word
  have hN : 1 + (n2 + (n3 + (n4 + (n5 + (n6 + 1))))) ≤ 60 * (HvdH.vsz v + 1) := by
    have h2 := hn2
    have h4 := hn4
    omega
  -- assembling the six steps
  let pc : HvdH.Cmd := Work.Kernel.pushGlyphs [HvdH.Glyph.cons] lfStBk lfQ
  have E6 : Ev main (seqs [pc]) ⟨s5.reg, s5.stk⟩ ⟨s6.reg, s6.stk⟩ (n6 + 1) :=
    Ev.seqs_cons he6' (Ev.seqs_nil (s := ⟨s6.reg, s6.stk⟩))
  have E56 : Ev main (seqs [pc, pc]) ⟨s4.reg, s4.stk⟩ ⟨s6.reg, s6.stk⟩ (n5 + (n6 + 1)) :=
    Ev.seqs_cons he5' E6
  have E456 : Ev main (seqs [mvVal lfStM1 lfStBk lfCA lfCB, pc, pc])
      ⟨s3.reg, s3.stk⟩ ⟨s6.reg, s6.stk⟩ (n4 + (n5 + (n6 + 1))) :=
    Ev.seqs_cons he4' E56
  have E3456 : Ev main (seqs [Work.Kernel.pushGlyphs [HvdH.Glyph.nil] lfStBk lfQ,
      mvVal lfStM1 lfStBk lfCA lfCB, pc, pc])
      ⟨s2.reg, s2.stk⟩ ⟨s6.reg, s6.stk⟩ (n3 + (n4 + (n5 + (n6 + 1)))) :=
    Ev.seqs_cons he3' E456
  have E23456 : Ev main (seqs [mvVal lfStF lfStM1 lfCA lfCB,
      Work.Kernel.pushGlyphs [HvdH.Glyph.nil] lfStBk lfQ,
      mvVal lfStM1 lfStBk lfCA lfCB, pc, pc])
      ⟨g1, X0⟩ ⟨s6.reg, s6.stk⟩ (n2 + (n3 + (n4 + (n5 + (n6 + 1))))) :=
    Ev.seqs_cons he2' E3456
  have Eall : Ev main (seqs [HvdH.Cmd.pop lfStF lfP, mvVal lfStF lfStM1 lfCA lfCB,
      Work.Kernel.pushGlyphs [HvdH.Glyph.nil] lfStBk lfQ,
      mvVal lfStM1 lfStBk lfCA lfCB, pc, pc])
      ⟨g, X⟩ ⟨s6.reg, s6.stk⟩ (1 + (n2 + (n3 + (n4 + (n5 + (n6 + 1)))))) :=
    Ev.seqs_cons hpop E23456
  refine ⟨⟨s6.reg, s6.stk⟩, 1 + (n2 + (n3 + (n4 + (n5 + (n6 + 1))))),
    ?_, hN, ?_, ?_, ?_⟩
  · rw [lfElemStep_unfold]
    exact Eall
  · -- `lfStF` holds the remaining list
    show s6.stk lfStF = rest
    rw [h6fr lfStF hFB, h5fr lfStF hFB, h4fr lfStF hFM hFB hFC hFD, h3fr lfStF hFB]
    exact h2F
  · -- `lfStBk` holds the extended row list
    show s6.stk lfStBk = (HvdH.ofList (HvdH.ofList [v] :: L)).enc ++ G
    have e3 : s3.stk lfStBk = HvdH.Glyph.nil :: s2.stk lfStBk := by simpa using h3Bk
    have e2 : s2.stk lfStBk = X lfStBk := by
      rw [h2fr lfStBk hFB.symm hMB.symm hBC hBD, hX0B]
    rw [h6Bk, h5Bk, h4Bk, e3, e2, hb]
    simp [HvdH.ofList, HvdH.Val.enc, List.append_assoc]
  · -- frame
    intro j hjF hjB
    show s6.stk j = X j
    have h64 : s6.stk j = s4.stk j := by rw [h6fr j hjB, h5fr j hjB]
    have h4X : s4.stk j = X0 j := by
      rcases eq_or_ne j lfStM1 with hM | hM
      · subst hM; exact h4M
      rcases eq_or_ne j lfCA with hC | hC
      · subst hC; rw [h4CA, h3fr lfCA hBC.symm, h2CA]
      rcases eq_or_ne j lfCB with hD | hD
      · subst hD; rw [h4CB, h3fr lfCB hBD.symm, h2CB]
      rw [h4fr j hM hjB hC hD, h3fr j hjB, h2fr j hjF hM hC hD]
    rw [h64, h4X]
    exact Function.update_of_ne hjF (v.enc ++ rest) X

end Work.SynFFT
