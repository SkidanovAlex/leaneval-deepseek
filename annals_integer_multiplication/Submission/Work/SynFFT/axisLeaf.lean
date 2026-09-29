import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.SynFFT.axisLeafDefs
import Submission.Work.SynFFT.axisLeafLoop
import Submission.Work.SynFFT.leafFinal
import Submission.Work.SynFFT.leafCost
import Submission.Work.SynFFT.leafSize

set_option autoImplicit false

namespace Work.SynFFT

open HvdH
open Work.Layout
open Work.Layout.AA

set_option maxHeartbeats 1600000 in
theorem axisLeaf : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (t B : ℕ)
    (blk : List HvdH.Val) (rest : List HvdH.Val),
  blk.length = t * B → 1 ≤ t → 1 ≤ B →
  HvdH.WordR main prog
    (fun vs => vs = HvdH.ofList blk :: HvdH.Val.int (t : ℤ) :: HvdH.Val.int (B : ℤ) :: rest)
    (fun _ out => out = stateVal ((rowsOf t B blk).map exploded) ::
      HvdH.Val.int (t : ℤ) :: HvdH.Val.int (B : ℤ) :: rest)
    (fun _ => K * (HvdH.vsz (HvdH.ofList blk) + 1) +
      K * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1)) := by
  obtain ⟨revP, Kr, hrev⟩ := Work.Layout.reverseWord
  refine ⟨lfMain revP, 1000000 + Kr, ?_⟩
  intro main t B blk rest hlen ht hB
  intro vs hvs s R hs
  subst hvs
  have hWlen : blk.reverse.length = t * B := by simpa using hlen
  -- (1) prologue
  obtain ⟨s1, n1, h1ev, hn1, h1mark, h1oth⟩ := lfPrologue_ev main s.reg s.stk
  have hs1 : s1.stk 0 = HvdH.encs (HvdH.ofList blk :: HvdH.Val.int (t : ℤ) ::
      HvdH.Val.int (B : ℤ) :: rest) ++ R := by
    rw [h1oth 0 (by decide)]; exact hs
  -- (2) reversal
  obtain ⟨out2, s2, n2, h2post, h2ev, hn2, h2stk0, h2oth⟩ :=
    hrev main blk (HvdH.ofList blk :: HvdH.Val.int (t : ℤ) :: HvdH.Val.int (B : ℤ) :: rest)
      ⟨HvdH.Val.int (t : ℤ) :: HvdH.Val.int (B : ℤ) :: rest, rfl⟩ s1 R hs1
  obtain ⟨r2, h2eq, h2out⟩ := h2post
  have hr2 : r2 = HvdH.Val.int (t : ℤ) :: HvdH.Val.int (B : ℤ) :: rest :=
    (List.cons.inj h2eq).2.symm
  have hout2 : out2 = HvdH.ofList blk.reverse ::
      HvdH.Val.int (t : ℤ) :: HvdH.Val.int (B : ℤ) :: rest := by rw [h2out, hr2]
  -- (3) setup
  obtain ⟨s3, n3, h3ev, hn3, h3c0, h3F, h3ca, h3cb, h3oth⟩ :=
    mvVal_ev' (main := main) (a := 0) (b := lfStF) (c := lfCA) (d := lfCB)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s2.reg) (X := s2.stk) (v := HvdH.ofList blk.reverse)
      (A := (HvdH.Val.int (t : ℤ)).enc ++ (HvdH.Val.int (B : ℤ)).enc ++
        HvdH.encs rest ++ R)
      (B := gMark :: s.stk lfStF)
      (by rw [h2stk0, hout2]; simp only [Work.Kernel.encs_cons, List.append_assoc])
      (by rw [h2oth lfStF (by decide), h1mark lfStF (by decide)])
  obtain ⟨s4, n4, h4ev, hn4, h4c0, h4ca, h4cb, h4m1, h4oth⟩ :=
    mvVal_ev' (main := main) (a := 0) (b := lfCA) (c := lfCB) (d := lfStM1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s3.reg) (X := s3.stk) (v := HvdH.Val.int (t : ℤ))
      (A := (HvdH.Val.int (B : ℤ)).enc ++ HvdH.encs rest ++ R)
      (B := s3.stk lfCA)
      (by rw [h3c0]; simp only [List.append_assoc])
      (by rfl)
  have h4t2 : s4.stk lfStT2 = gMark :: s.stk lfStT2 := by
    rw [h4oth lfStT2 (by decide) (by decide), h3oth lfStT2 (by decide) (by decide),
      h2oth lfStT2 (by decide), h1mark lfStT2 (by decide)]
  have h4t5 : s4.stk lfStT5 = gMark :: s.stk lfStT5 := by
    rw [h4oth lfStT5 (by decide) (by decide), h3oth lfStT5 (by decide) (by decide),
      h2oth lfStT5 (by decide), h1mark lfStT5 (by decide)]
  have h4el : s4.stk lfStEl = gMark :: s.stk lfStEl := by
    rw [h4oth lfStEl (by decide) (by decide), h3oth lfStEl (by decide) (by decide),
      h2oth lfStEl (by decide), h1mark lfStEl (by decide)]
  have h4t4 : s4.stk lfStT4 = gMark :: s.stk lfStT4 := by
    rw [h4oth lfStT4 (by decide) (by decide), h3oth lfStT4 (by decide) (by decide),
      h2oth lfStT4 (by decide), h1mark lfStT4 (by decide)]
  have h4bk : s4.stk lfStBk = gMark :: s.stk lfStBk := by
    rw [h4oth lfStBk (by decide) (by decide), h3oth lfStBk (by decide) (by decide),
      h2oth lfStBk (by decide), h1mark lfStBk (by decide)]
  have h4bl : s4.stk lfStBl = gMark :: s.stk lfStBl := by
    rw [h4oth lfStBl (by decide) (by decide), h3oth lfStBl (by decide) (by decide),
      h2oth lfStBl (by decide), h1mark lfStBl (by decide)]
  -- 3c: copy int B to lfStEl
  obtain ⟨s5, n5, h5ev, hn5, h5c0, h5el, h5t5, h5oth⟩ :=
    copyIntTo_ev2 main 0 lfStEl lfStT5 lfC1 lfF (by decide) (by decide) (by decide) (by decide)
      s4.reg s4.stk B (HvdH.encs rest ++ R) (gMark :: s.stk lfStEl) (s.stk lfStT5)
      (by rw [h4c0]; simp only [List.append_assoc]) h4el h4t5
  -- 3d: copy int B to lfStT4
  have h5t4 : s5.stk lfStT4 = gMark :: s.stk lfStT4 := by
    rw [h5oth lfStT4 (by decide) (by decide) (by decide), h4t4]
  obtain ⟨s6, n6, h6ev, hn6, h6el, h6t4, h6t5, h6oth⟩ :=
    copyIntTo_ev2 main lfStEl lfStT4 lfStT5 lfC1 lfF (by decide) (by decide) (by decide) (by decide)
      s5.reg s5.stk B (gMark :: s.stk lfStEl) (gMark :: s.stk lfStT4) (s.stk lfStT5)
      h5el h5t4 h5t5
  -- 3e: move int t back to stack 0
  have h6ca : s6.stk lfCA = (HvdH.Val.int (t : ℤ)).enc ++ s.stk lfCA := by
    rw [h6oth lfCA (by decide) (by decide) (by decide),
      h5oth lfCA (by decide) (by decide) (by decide), h4ca,
      h3oth lfCA (by decide) (by decide), h2oth lfCA (by decide), h1oth lfCA (by decide)]
  obtain ⟨s7, n7, h7ev, hn7, h7ca, h7c0, h7cb, h7m1, h7oth⟩ :=
    mvVal_ev' (main := main) (a := lfCA) (b := 0) (c := lfCB) (d := lfStM1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s6.reg) (X := s6.stk) (v := HvdH.Val.int (t : ℤ))
      (A := s.stk lfCA)
      (B := (HvdH.Val.int (B : ℤ)).enc ++ HvdH.encs rest ++ R)
      (by rw [h6ca])
      (by rw [h6oth 0 (by decide) (by decide) (by decide), h5c0]; simp only [List.append_assoc])
  have h7t : s7.stk lfStT2 = gMark :: s.stk lfStT2 := by
    rw [h7oth lfStT2 (by decide) (by decide),
      h6oth lfStT2 (by decide) (by decide) (by decide),
      h5oth lfStT2 (by decide) (by decide) (by decide), h4t2]
  have h7t5 : s7.stk lfStT5 = gMark :: s.stk lfStT5 := by
    rw [h7oth lfStT5 (by decide) (by decide), h6t5]
  have h7el : s7.stk lfStEl = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: s.stk lfStEl := by
    rw [h7oth lfStEl (by decide) (by decide), h6el]
  have h7t4 : s7.stk lfStT4 = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: s.stk lfStT4 := by
    rw [h7oth lfStT4 (by decide) (by decide), h6t4]
  have h7F : s7.stk lfStF = (HvdH.ofList blk.reverse).enc ++ gMark :: s.stk lfStF := by
    rw [h7oth lfStF (by decide) (by decide),
      h6oth lfStF (by decide) (by decide) (by decide),
      h5oth lfStF (by decide) (by decide) (by decide),
      h4oth lfStF (by decide) (by decide), h3F]
  obtain ⟨s8, n8, h8ev, hn8, h8bk, h8oth⟩ := pushNil_ev main lfStBk lfQ s7.reg s7.stk
  obtain ⟨s9, n9, h9ev, hn9, h9bl, h9oth⟩ := pushNil_ev main lfStBl lfQ s8.reg s8.stk
  have h9F : s9.stk lfStF = (HvdH.ofList blk.reverse).enc ++ gMark :: s.stk lfStF := by
    rw [h9oth lfStF (by decide), h8oth lfStF (by decide), h7F]
  have h9Bk : s9.stk lfStBk = (HvdH.ofList []).enc ++ gMark :: s.stk lfStBk := by
    rw [h9oth lfStBk (by decide), h8bk,
      h7oth lfStBk (by decide) (by decide),
      h6oth lfStBk (by decide) (by decide) (by decide),
      h5oth lfStBk (by decide) (by decide) (by decide), h4bk]
  have h9Bl : s9.stk lfStBl = (HvdH.ofList []).enc ++ gMark :: s.stk lfStBl := by
    rw [h9bl, h8oth lfStBl (by decide),
      h7oth lfStBl (by decide) (by decide),
      h6oth lfStBl (by decide) (by decide) (by decide),
      h5oth lfStBl (by decide) (by decide) (by decide), h4bl]
  have h9T4 : s9.stk lfStT4 = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: s.stk lfStT4 := by
    rw [h9oth lfStT4 (by decide), h8oth lfStT4 (by decide), h7t4]
  have h9T2 : s9.stk lfStT2 = gMark :: s.stk lfStT2 := by
    rw [h9oth lfStT2 (by decide), h8oth lfStT2 (by decide), h7t]
  have h9T5 : s9.stk lfStT5 = gMark :: s.stk lfStT5 := by
    rw [h9oth lfStT5 (by decide), h8oth lfStT5 (by decide), h7t5]
  have h9El : s9.stk lfStEl = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: s.stk lfStEl := by
    rw [h9oth lfStEl (by decide), h8oth lfStEl (by decide), h7el]
  have h9c0 : s9.stk 0 = (HvdH.Val.int (t : ℤ)).enc ++ (HvdH.Val.int (B : ℤ)).enc ++
      HvdH.encs rest ++ R := by
    rw [h9oth 0 (by decide), h8oth 0 (by decide), h7c0]
    simp only [List.append_assoc]
  -- (4) the loop
  let Z : HvdH.Stk → List HvdH.Glyph :=
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s9.stk lfStF (s.stk lfStF)) lfStBk (s.stk lfStBk))
      lfStBl (s.stk lfStBl)) lfStT4 (s.stk lfStT4)) lfStT2 (s.stk lfStT2))
      lfStT5 (s.stk lfStT5)) lfStEl (s.stk lfStEl)
  have hZF : Z lfStF = s.stk lfStF := by
    simp only [Z]
    rw [Function.update_of_ne (by decide : (lfStF : HvdH.Stk) ≠ lfStEl),
      Function.update_of_ne (by decide : (lfStF : HvdH.Stk) ≠ lfStT5),
      Function.update_of_ne (by decide : (lfStF : HvdH.Stk) ≠ lfStT2),
      Function.update_of_ne (by decide : (lfStF : HvdH.Stk) ≠ lfStT4),
      Function.update_of_ne (by decide : (lfStF : HvdH.Stk) ≠ lfStBl),
      Function.update_of_ne (by decide : (lfStF : HvdH.Stk) ≠ lfStBk),
      Function.update_self]
  have hZBk : Z lfStBk = s.stk lfStBk := by
    simp only [Z]
    rw [Function.update_of_ne (by decide : (lfStBk : HvdH.Stk) ≠ lfStEl),
      Function.update_of_ne (by decide : (lfStBk : HvdH.Stk) ≠ lfStT5),
      Function.update_of_ne (by decide : (lfStBk : HvdH.Stk) ≠ lfStT2),
      Function.update_of_ne (by decide : (lfStBk : HvdH.Stk) ≠ lfStT4),
      Function.update_of_ne (by decide : (lfStBk : HvdH.Stk) ≠ lfStBl),
      Function.update_self]
  have hZBl : Z lfStBl = s.stk lfStBl := by
    simp only [Z]
    rw [Function.update_of_ne (by decide : (lfStBl : HvdH.Stk) ≠ lfStEl),
      Function.update_of_ne (by decide : (lfStBl : HvdH.Stk) ≠ lfStT5),
      Function.update_of_ne (by decide : (lfStBl : HvdH.Stk) ≠ lfStT2),
      Function.update_of_ne (by decide : (lfStBl : HvdH.Stk) ≠ lfStT4),
      Function.update_self]
  have hZT4 : Z lfStT4 = s.stk lfStT4 := by
    simp only [Z]
    rw [Function.update_of_ne (by decide : (lfStT4 : HvdH.Stk) ≠ lfStEl),
      Function.update_of_ne (by decide : (lfStT4 : HvdH.Stk) ≠ lfStT5),
      Function.update_of_ne (by decide : (lfStT4 : HvdH.Stk) ≠ lfStT2),
      Function.update_self]
  have hZT2 : Z lfStT2 = s.stk lfStT2 := by
    simp only [Z]
    rw [Function.update_of_ne (by decide : (lfStT2 : HvdH.Stk) ≠ lfStEl),
      Function.update_of_ne (by decide : (lfStT2 : HvdH.Stk) ≠ lfStT5),
      Function.update_self]
  have hZT5 : Z lfStT5 = s.stk lfStT5 := by
    simp only [Z]
    rw [Function.update_of_ne (by decide : (lfStT5 : HvdH.Stk) ≠ lfStEl),
      Function.update_self]
  have hZEl : Z lfStEl = s.stk lfStEl := by
    simp only [Z]
    rw [Function.update_self]
  have hZoth : ∀ k, k ≠ lfStF → k ≠ lfStBk → k ≠ lfStBl → k ≠ lfStT4 → k ≠ lfStT2 →
      k ≠ lfStT5 → k ≠ lfStEl → Z k = s9.stk k := by
    intro k h1 h2 h3 h4 h5 h6 h7
    simp only [Z]
    rw [Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5,
      Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
      Function.update_of_ne h1]
  obtain ⟨s10, hrun10, h10reg, h10F, h10Bk, h10Bl, h10T4, h10T2, h10T5, h10El, h10oth⟩ :=
    lfLoop_run main t B blk.reverse hWlen hB blk.reverse [] rfl [] [] B 0
      (Function.update s9.reg lfF HvdH.Glyph.cons) s9.stk Z
      (by simp [lfRowL]) (by simp [lfRowsL])
      (by simp) (by simp)
      (by rw [h9F, hZF]) (by rw [h9Bk, hZBk]) (by rw [h9Bl, hZBl]) (by rw [h9T4, hZT4])
      (by rw [h9T2, hZT2]) (by rw [h9T5, hZT5]) (by rw [h9El, hZEl])
      (by intro k h1 h2 h3 h4 h5 h6 h7
          rw [hZoth k h1 h2 h3 h4 h5 h6 h7])
      (by simp)
  have hloopEv : Ev main (.loop lfF HvdH.Glyph.cons lfBody)
      ⟨Function.update s9.reg lfF HvdH.Glyph.cons, s9.stk⟩ s10
      (lfTC B blk.reverse B 0 + 2 + 1) :=
    loopRuns.eval hrun10 (by rw [h10reg]; decide)
  -- (5) finish
  have h10c0 : s10.stk 0 = (HvdH.Val.int (t : ℤ)).enc ++ (HvdH.Val.int (B : ℤ)).enc ++
      HvdH.encs rest ++ R := by
    rw [h10oth 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hZoth 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h9c0]
  obtain ⟨s11, n11, h11ev, hn11, h11bl, h11c0, h11ca, h11cb, h11oth⟩ :=
    mvVal_ev' (main := main) (a := lfStBl) (b := 0) (c := lfCA) (d := lfCB)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s10.reg) (X := s10.stk) (v := HvdH.ofList (lfRowsL t B blk.reverse blk.reverse))
      (A := gMark :: s.stk lfStBl)
      (B := (HvdH.Val.int (t : ℤ)).enc ++ (HvdH.Val.int (B : ℤ)).enc ++ HvdH.encs rest ++ R)
      (by rw [h10Bl, hZBl])
      (by rw [h10c0])
  have h11F : s11.stk lfStF = (HvdH.ofList []).enc ++ gMark :: s.stk lfStF := by
    rw [h11oth lfStF (by decide) (by decide), h10F, hZF]
  have h11Bk : s11.stk lfStBk = (HvdH.ofList []).enc ++ gMark :: s.stk lfStBk := by
    rw [h11oth lfStBk (by decide) (by decide), h10Bk, hZBk]
  have h11Bl : s11.stk lfStBl = gMark :: s.stk lfStBl := by
    rw [h11bl]
  have h11T4 : s11.stk lfStT4 = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: s.stk lfStT4 := by
    rw [h11oth lfStT4 (by decide) (by decide), h10T4, hZT4]
  have h11T2 : s11.stk lfStT2 = gMark :: s.stk lfStT2 := by
    rw [h11oth lfStT2 (by decide) (by decide), h10T2, hZT2]
  have h11T5 : s11.stk lfStT5 = gMark :: s.stk lfStT5 := by
    rw [h11oth lfStT5 (by decide) (by decide), h10T5, hZT5]
  have h11El : s11.stk lfStEl = (HvdH.Val.int (B : ℤ)).enc ++ gMark :: s.stk lfStEl := by
    rw [h11oth lfStEl (by decide) (by decide), h10El, hZEl]
  -- epilogue: 7 clearTo steps
  obtain ⟨s12, n12, h12ev, hn12, h12F, h12oth⟩ :=
    clearTo_ev main lfStF lfP lfF (by decide) s11.reg s11.stk ((HvdH.ofList []).enc)
      (s.stk lfStF) (by decide) h11F
  obtain ⟨s13, n13, h13ev, hn13, h13Bk, h13oth⟩ :=
    clearTo_ev main lfStBk lfP lfF (by decide) s12.reg s12.stk ((HvdH.ofList []).enc)
      (s.stk lfStBk) (by decide)
      (by rw [h12oth lfStBk (by decide), h11Bk]; rfl)
  obtain ⟨s14, n14, h14ev, hn14, h14Bl, h14oth⟩ :=
    clearTo_ev main lfStBl lfP lfF (by decide) s13.reg s13.stk ([] : List HvdH.Glyph)
      (s.stk lfStBl) (by simp)
      (by rw [h13oth lfStBl (by decide), h12oth lfStBl (by decide), h11Bl]; rfl)
  obtain ⟨s15, n15, h15ev, hn15, h15T4, h15oth⟩ :=
    clearTo_ev main lfStT4 lfP lfF (by decide) s14.reg s14.stk ((HvdH.Val.int (B : ℤ)).enc)
      (s.stk lfStT4) (Work.Layout.gMark_not_mem_enc _)
      (by rw [h14oth lfStT4 (by decide), h13oth lfStT4 (by decide), h12oth lfStT4 (by decide),
        h11T4]; rfl)
  obtain ⟨s16, n16, h16ev, hn16, h16T2, h16oth⟩ :=
    clearTo_ev main lfStT2 lfP lfF (by decide) s15.reg s15.stk ([] : List HvdH.Glyph)
      (s.stk lfStT2) (by simp)
      (by rw [h15oth lfStT2 (by decide), h14oth lfStT2 (by decide), h13oth lfStT2 (by decide),
        h12oth lfStT2 (by decide), h11T2]; rfl)
  obtain ⟨s17, n17, h17ev, hn17, h17T5, h17oth⟩ :=
    clearTo_ev main lfStT5 lfP lfF (by decide) s16.reg s16.stk ([] : List HvdH.Glyph)
      (s.stk lfStT5) (by simp)
      (by rw [h16oth lfStT5 (by decide), h15oth lfStT5 (by decide), h14oth lfStT5 (by decide),
        h13oth lfStT5 (by decide), h12oth lfStT5 (by decide), h11T5]; rfl)
  obtain ⟨s18, n18, h18ev, hn18, h18El, h18oth⟩ :=
    clearTo_ev main lfStEl lfP lfF (by decide) s17.reg s17.stk ((HvdH.Val.int (B : ℤ)).enc)
      (s.stk lfStEl) (Work.Layout.gMark_not_mem_enc _)
      (by rw [h17oth lfStEl (by decide), h16oth lfStEl (by decide), h15oth lfStEl (by decide),
        h14oth lfStEl (by decide), h13oth lfStEl (by decide), h12oth lfStEl (by decide),
        h11El]; rfl)
  -- composed Ev's
  have hSetupEv : Ev main lfSetup s2 s9 (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9)))))) := by
    unfold lfSetup
    simp only [seqs]
    exact Ev.seq h3ev (Ev.seq h4ev (Ev.seq h5ev (Ev.seq h6ev (Ev.seq h7ev
      (Ev.seq h8ev h9ev)))))
  have hLoopEv : Ev main lfLoop s9 s10 (1 + (lfTC B blk.reverse B 0 + 2 + 1)) := by
    unfold lfLoop
    simp only [seqs]
    exact Ev.seq (ev_set' main lfF HvdH.Glyph.cons s9.reg s9.stk) hloopEv
  have hFinishEv : Ev main lfFinish s10 s18
      (n11 + (n12 + (n13 + (n14 + (n15 + (n16 + (n17 + n18))))))) := by
    unfold lfFinish lfEpilogue
    simp only [lfStks, List.map_cons, List.map_nil, seqs]
    exact Ev.seq h11ev (Ev.seq h12ev (Ev.seq h13ev (Ev.seq h14ev (Ev.seq h15ev (Ev.seq h16ev
      (Ev.seq h17ev h18ev))))))
  have hAll : Ev main (lfMain revP) ⟨s.reg, s.stk⟩ s18
      (n1 + (n2 + ((n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9)))))) +
        ((1 + (lfTC B blk.reverse B 0 + 2 + 1)) +
        (n11 + (n12 + (n13 + (n14 + (n15 + (n16 + (n17 + n18))))))))))) := by
    unfold lfMain
    simp only [seqs]
    exact Ev.seq h1ev (Ev.seq ⟨n2, h2ev, le_rfl⟩ (Ev.seq hSetupEv (Ev.seq hLoopEv hFinishEv)))
  -- the output value
  have hout : HvdH.ofList (lfRowsL t B blk.reverse blk.reverse) =
      stateVal ((rowsOf t B blk).map exploded) := by
    rw [leafRowsL.2.2 t B blk.reverse hB hWlen]
    exact leafFinal.1 t B blk hlen ht hB
  obtain ⟨hc1, hc2⟩ := leafCost
  have hsz := leafSize t B blk hlen ht hB
  have htc : lfTC B blk.reverse B 0 ≤ 1000 * (HvdH.vsz (HvdH.ofList blk) + 1) +
      1000 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) :=
    le_trans (hc1 B 0 B blk.reverse hB le_rfl) (hc2 t B blk hlen ht hB)
  have hvsz0 : 1 ≤ HvdH.vsz (HvdH.ofList blk) := by
    have h := leafFinal.2.1 blk
    have h2 : 0 ≤ (blk.map HvdH.vsz).sum := Nat.zero_le _
    omega
  have hvszblk : HvdH.vsz (HvdH.ofList blk) =
      (blk.map HvdH.vsz).sum + blk.length + 1 := leafFinal.2.1 blk
  have hvszrev : HvdH.vsz (HvdH.ofList blk.reverse) = HvdH.vsz (HvdH.ofList blk) := by
    rw [leafFinal.2.1 blk.reverse, hvszblk]
    simp only [List.map_reverse, List.sum_reverse, List.length_reverse]
  have hiszt : HvdH.isz (t : ℤ) ≤ t + 2 := by
    simp only [HvdH.isz, Int.natAbs_natCast]
    have := nat_size_le_self t
    omega
  have hiszB : 2 ≤ HvdH.isz (B : ℤ) := by
    simp only [HvdH.isz]
    omega
  -- (6) cost bookkeeping
  have hN : 1 ≤ blk.length := by
    rw [hlen]
    simpa using Nat.mul_le_mul ht hB
  have hsz := leafSize t B blk hlen ht hB
  have hcostAll : n1 + (n2 + ((n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9)))))) +
        ((1 + (lfTC B blk.reverse B 0 + 2 + 1)) +
        (n11 + (n12 + (n13 + (n14 + (n15 + (n16 + (n17 + n18)))))))))) ≤
      (1000000 + Kr) * (HvdH.vsz (HvdH.ofList blk) + 1) + (1000000 + Kr) * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
    have hV1 : 1 ≤ (HvdH.vsz (HvdH.ofList blk) + 1) := Nat.le_add_left 1 _
    have hP1 : 1 ≤ ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := Nat.le_add_left 1 _
    have hV2 : 2 ≤ (HvdH.vsz (HvdH.ofList blk) + 1) := by
      have := one_le_vsz (HvdH.ofList blk); omega
    have hmulP : 1 ≤ (blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) := by
      have h := Nat.mul_le_mul (show 1 ≤ blk.length + t + 1 by omega)
        (show 1 ≤ HvdH.isz (B : ℤ) + 1 by omega)
      simpa using h
    have hP2 : 2 ≤ ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by omega
    have hiztP : HvdH.isz (t : ℤ) + 1 ≤ ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have hsT : HvdH.isz (t : ℤ) ≤ t + 2 := by
        have h := nat_size_le_self t
        simp only [HvdH.isz, Int.natAbs_natCast]
        omega
      have h1 : t + 2 ≤ blk.length + t + 1 := by omega
      have h2 : 3 ≤ HvdH.isz (B : ℤ) + 1 := by omega
      have hmul : (t + 2) * 3 ≤ (blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) :=
        Nat.mul_le_mul h1 h2
      omega
    have hizBP : HvdH.isz (B : ℤ) + 1 ≤ ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h1 : 2 ≤ blk.length + t + 1 := by omega
      have hmul : 2 * (HvdH.isz (B : ℤ) + 1) ≤
          (blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) := Nat.mul_le_mul h1 le_rfl
      have h2 : 1 ≤ HvdH.isz (B : ℤ) + 1 := by omega
      omega
    have hlenB : (HvdH.Val.int (B : ℤ)).enc.length = HvdH.isz (B : ℤ) := by
      change HvdH.vsz (HvdH.Val.int (B : ℤ)) = HvdH.isz (B : ℤ)
      exact vsz_int (B : ℤ)
    have h1n : n1 ≤ 22 := hn1
    have h2n : n2 ≤ Kr * (HvdH.vsz (HvdH.ofList blk) + 1) := hn2
    have h3n : n3 ≤ 16 * (HvdH.vsz (HvdH.ofList blk) + 1) := by
      rw [hvszrev] at hn3
      exact hn3
    have h4n : n4 ≤ 16 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := hn4
      rw [vsz_int] at h
      omega
    have h5n : n5 ≤ 16 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by omega
    have h6n : n6 ≤ 16 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by omega
    have h7n : n7 ≤ 16 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := hn7
      rw [vsz_int] at h
      omega
    have h8n : n8 ≤ 5 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by omega
    have h9n : n9 ≤ 5 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by omega
    have hLn : 1 + (lfTC B blk.reverse B 0 + 2 + 1) ≤ 1001 * (HvdH.vsz (HvdH.ofList blk) + 1) + 1001 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := htc
      omega
    have h11n : n11 ≤ 160 * (HvdH.vsz (HvdH.ofList blk) + 1) := by
      have h := hn11
      omega
    have h12n : n12 ≤ 14 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := hn12
      have h0 : (HvdH.ofList ([] : List HvdH.Val)).enc.length = 1 := rfl
      rw [h0] at h
      omega
    have h13n : n13 ≤ 14 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := hn13
      have h0 : (HvdH.ofList ([] : List HvdH.Val)).enc.length = 1 := rfl
      rw [h0] at h
      omega
    have h14n : n14 ≤ 9 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := hn14
      have h0 : ([] : List HvdH.Glyph).length = 0 := rfl
      rw [h0] at h
      omega
    have h15n : n15 ≤ 10 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := hn15
      rw [hlenB] at h
      omega
    have h16n : n16 ≤ 9 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := hn16
      have h0 : ([] : List HvdH.Glyph).length = 0 := rfl
      rw [h0] at h
      omega
    have h17n : n17 ≤ 9 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := hn17
      have h0 : ([] : List HvdH.Glyph).length = 0 := rfl
      rw [h0] at h
      omega
    have h18n : n18 ≤ 10 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have h := hn18
      rw [hlenB] at h
      omega
    have hsum : n1 + (n2 + ((n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9)))))) +
        ((1 + (lfTC B blk.reverse B 0 + 2 + 1)) +
        (n11 + (n12 + (n13 + (n14 + (n15 + (n16 + (n17 + n18)))))))))) ≤ 1177 * (HvdH.vsz (HvdH.ofList blk) + 1) + 1150 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) + Kr * (HvdH.vsz (HvdH.ofList blk) + 1) + 22 := by omega
    have hfin : 1177 * (HvdH.vsz (HvdH.ofList blk) + 1) + 1150 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) + Kr * (HvdH.vsz (HvdH.ofList blk) + 1) + 22 ≤
        (1000000 + Kr) * (HvdH.vsz (HvdH.ofList blk) + 1) + (1000000 + Kr) * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by
      have hKV : (1000000 + Kr) * (HvdH.vsz (HvdH.ofList blk) + 1) = 1000000 * (HvdH.vsz (HvdH.ofList blk) + 1) + Kr * (HvdH.vsz (HvdH.ofList blk) + 1) := by ring
      have hKP : (1000000 + Kr) * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) = 1000000 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) + Kr * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1) := by ring
      rw [hKV, hKP]
      omega
    exact le_trans hsum hfin
  have hAll' := Ev.mono hAll hcostAll
  obtain ⟨nall, hEvalAll, hcostAll'⟩ := hAll'
  have h18s : ∀ j : HvdH.Stk, j ∈ lfStks → s18.stk j = s.stk j := by
    intro j hj
    simp only [lfStks, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h18oth lfStF (by decide), h17oth lfStF (by decide), h16oth lfStF (by decide),
        h15oth lfStF (by decide), h14oth lfStF (by decide), h13oth lfStF (by decide), h12F]
    · rw [h18oth lfStBk (by decide), h17oth lfStBk (by decide), h16oth lfStBk (by decide),
        h15oth lfStBk (by decide), h14oth lfStBk (by decide), h13Bk]
    · rw [h18oth lfStBl (by decide), h17oth lfStBl (by decide), h16oth lfStBl (by decide),
        h15oth lfStBl (by decide), h14Bl]
    · rw [h18oth lfStT4 (by decide), h17oth lfStT4 (by decide), h16oth lfStT4 (by decide), h15T4]
    · rw [h18oth lfStT2 (by decide), h17oth lfStT2 (by decide), h16T2]
    · rw [h18oth lfStT5 (by decide), h17T5]
    · rw [h18El]
  refine ⟨stateVal ((rowsOf t B blk).map exploded) ::
      HvdH.Val.int (t : ℤ) :: HvdH.Val.int (B : ℤ) :: rest, s18, nall, ?_, hEvalAll,
      hcostAll', ?_, ?_⟩
  · rfl
  · rw [h18oth 0 (by decide), h17oth 0 (by decide), h16oth 0 (by decide), h15oth 0 (by decide),
      h14oth 0 (by decide), h13oth 0 (by decide), h12oth 0 (by decide), h11c0,
      Work.Kernel.encs_cons, Work.Kernel.encs_cons, Work.Kernel.encs_cons, hout]
    simp only [List.append_assoc]
  · intro k hk0
    by_cases hmem : k ∈ lfStks
    · exact h18s k hmem
    · have hne : ∀ j : HvdH.Stk, j ∈ lfStks → k ≠ j := fun j hj h => hmem (by rw [h]; exact hj)
      rw [h18oth k (hne lfStEl (by decide)), h17oth k (hne lfStT5 (by decide)),
        h16oth k (hne lfStT2 (by decide)), h15oth k (hne lfStT4 (by decide)),
        h14oth k (hne lfStBl (by decide)), h13oth k (hne lfStBk (by decide)),
        h12oth k (hne lfStF (by decide)),
        h11oth k (hne lfStBl (by decide)) hk0,
        h10oth k (hne lfStF (by decide)) (hne lfStBk (by decide)) (hne lfStBl (by decide))
          (hne lfStT4 (by decide)) (hne lfStT2 (by decide)) (hne lfStT5 (by decide))
          (hne lfStEl (by decide)),
        hZoth k (hne lfStF (by decide)) (hne lfStBk (by decide)) (hne lfStBl (by decide))
          (hne lfStT4 (by decide)) (hne lfStT2 (by decide)) (hne lfStT5 (by decide))
          (hne lfStEl (by decide)),
        h9oth k (hne lfStBl (by decide)), h8oth k (hne lfStBk (by decide))]
      by_cases hkca : k = lfCA
      · subst hkca
        rw [h7ca]
      · rw [h7oth k hkca hk0,
          h6oth k (hne lfStEl (by decide)) (hne lfStT4 (by decide)) (hne lfStT5 (by decide)),
          h5oth k hk0 (hne lfStEl (by decide)) (hne lfStT5 (by decide)),
          h4oth k hk0 hkca, h3oth k hk0 (hne lfStF (by decide)), h2oth k hk0, h1oth k hmem]

end Work.SynFFT
