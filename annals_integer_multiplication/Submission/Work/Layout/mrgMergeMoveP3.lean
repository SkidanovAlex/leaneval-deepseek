import Mathlib
import Submission.Work.Layout.mrgDefs
import Submission.Work.Layout.mrgUpdSize
import Submission.Work.Layout.merge_updSizeSkip

namespace Work.Layout

theorem mrgMergeMoveP3 {main pSize : HvdH.Cmd} {KSz : ℕ}
    (hSz : ∀ main : HvdH.Cmd, HvdH.UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ))
      (fun a => KSz * HvdH.isz a))
    {SX SY T SA SB F1 F2 t d : HvdH.Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List HvdH.Stk).Nodup)
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph} {k : ℕ} {v' : HvdH.Val}
    {ps : List HvdH.Val} {A Tc R : List HvdH.Glyph}
    (hps : ∀ v ∈ ps, ∃ (k' : ℕ) (v'' : HvdH.Val), v = HvdH.Val.cons (HvdH.Val.int (k' : ℤ)) v'')
    (hSX : X SX = (HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v').enc ++ HvdH.encs ps ++ Work.Layout.gMark :: A)
    (hT : X T = Tc) (h0 : X 0 = R) :
    ∃ s' n, Work.Layout.Ev main (seqs [ Work.Layout.mvVal SX T t d, Work.Layout.Sk.updSize pSize SX SA t d ]) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (HvdH.vsz (HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v') + 1)
            + (if ps = [] then 4 else Work.Layout.updSizeCost KSz (Work.Layout.keyOf (ps.headD HvdH.Val.nil))) ∧
      s'.stk SX = HvdH.encs ps ++ Work.Layout.gMark :: A ∧
      s'.stk SY = X SY ∧
      s'.stk T = (HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v').enc ++ Tc ∧
      s'.stk 0 = R ∧
      s'.stk SA = (if ps = [] then X SA
                   else (HvdH.Val.int ((Work.Layout.keyOf (ps.headD HvdH.Val.nil)).size : ℤ)).enc ++ X SA) ∧
      s'.stk SB = X SB ∧
      s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k' : HvdH.Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset HvdH.Stk) → s'.stk k' = X k') := by
  -- pairwise distinctness of the nine stacks and `0` (from `hdis`)
  have hSXT : SX ≠ T := by intro h; rw [h] at hdis; simp at hdis
  have hSXt : SX ≠ t := by intro h; rw [h] at hdis; simp at hdis
  have hSXd : SX ≠ d := by intro h; rw [h] at hdis; simp at hdis
  have hTt : T ≠ t := by intro h; rw [h] at hdis; simp at hdis
  have hTd : T ≠ d := by intro h; rw [h] at hdis; simp at hdis
  have htd : t ≠ d := by intro h; rw [h] at hdis; simp at hdis
  have hSXSA : SX ≠ SA := by intro h; rw [h] at hdis; simp at hdis
  have hSX0 : SX ≠ 0 := by intro h; rw [h] at hdis; simp at hdis
  have hSA0 : SA ≠ 0 := by intro h; rw [h] at hdis; simp at hdis
  have hSAt : SA ≠ t := by intro h; rw [h] at hdis; simp at hdis
  have hSAd : SA ≠ d := by intro h; rw [h] at hdis; simp at hdis
  have h0t : (0 : HvdH.Stk) ≠ t := by intro h; rw [h] at hdis; simp at hdis
  have h0d : (0 : HvdH.Stk) ≠ d := by intro h; rw [h] at hdis; simp at hdis
  have hSAT : SA ≠ T := by intro h; rw [h] at hdis; simp at hdis
  have hSYSX : SY ≠ SX := by intro h; rw [h] at hdis; simp at hdis
  have hSYT : SY ≠ T := by intro h; rw [h] at hdis; simp at hdis
  have hSYt : SY ≠ t := by intro h; rw [h] at hdis; simp at hdis
  have hSYd : SY ≠ d := by intro h; rw [h] at hdis; simp at hdis
  have hSYSA : SY ≠ SA := by intro h; rw [h] at hdis; simp at hdis
  have hSY0 : SY ≠ 0 := by intro h; rw [h] at hdis; simp at hdis
  have hTSX : T ≠ SX := by intro h; rw [h] at hdis; simp at hdis
  have hTSA : T ≠ SA := by intro h; rw [h] at hdis; simp at hdis
  have hT0 : T ≠ 0 := by intro h; rw [h] at hdis; simp at hdis
  have hSBSX : SB ≠ SX := by intro h; rw [h] at hdis; simp at hdis
  have hSBT : SB ≠ T := by intro h; rw [h] at hdis; simp at hdis
  have hSBt : SB ≠ t := by intro h; rw [h] at hdis; simp at hdis
  have hSBd : SB ≠ d := by intro h; rw [h] at hdis; simp at hdis
  have hSBSA : SB ≠ SA := by intro h; rw [h] at hdis; simp at hdis
  have hSB0 : SB ≠ 0 := by intro h; rw [h] at hdis; simp at hdis
  have hF1SX : F1 ≠ SX := by intro h; rw [h] at hdis; simp at hdis
  have hF1T : F1 ≠ T := by intro h; rw [h] at hdis; simp at hdis
  have hF1t : F1 ≠ t := by intro h; rw [h] at hdis; simp at hdis
  have hF1d : F1 ≠ d := by intro h; rw [h] at hdis; simp at hdis
  have hF1SA : F1 ≠ SA := by intro h; rw [h] at hdis; simp at hdis
  have hF10 : F1 ≠ 0 := by intro h; rw [h] at hdis; simp at hdis
  have hF2SX : F2 ≠ SX := by intro h; rw [h] at hdis; simp at hdis
  have hF2T : F2 ≠ T := by intro h; rw [h] at hdis; simp at hdis
  have hF2t : F2 ≠ t := by intro h; rw [h] at hdis; simp at hdis
  have hF2d : F2 ≠ d := by intro h; rw [h] at hdis; simp at hdis
  have hF2SA : F2 ≠ SA := by intro h; rw [h] at hdis; simp at hdis
  have hF20 : F2 ≠ 0 := by intro h; rw [h] at hdis; simp at hdis
  have h0SX : (0 : HvdH.Stk) ≠ SX := by intro h; rw [h] at hdis; simp at hdis
  have h0T : (0 : HvdH.Stk) ≠ T := by intro h; rw [h] at hdis; simp at hdis
  -- the front record of `SX` is moved to `T`
  obtain ⟨s1, n1, h1ev, hn1, h1SX, h1T, h1t, h1d, h1fr⟩ :=
    mvVal_ev_full (main := main) (a := SX) (b := T) (c := t) (d := d) hSXT hSXt hSXd hTt hTd htd
      (g := g) (X := X) (v := HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v')
      (A := HvdH.encs ps ++ gMark :: A) (B := Tc)
      (hSX.trans (List.append_assoc _ _ _)) hT
  have h1SA : s1.stk SA = X SA := h1fr SA hSXSA.symm hSAT hSAt hSAd
  have h1SY : s1.stk SY = X SY := h1fr SY hSYSX hSYT hSYt hSYd
  have h1SB : s1.stk SB = X SB := h1fr SB hSBSX hSBT hSBt hSBd
  have h1F1 : s1.stk F1 = X F1 := h1fr F1 hF1SX hF1T hF1t hF1d
  have h1F2 : s1.stk F2 = X F2 := h1fr F2 hF2SX hF2T hF2t hF2d
  have h10 : s1.stk 0 = R := (h1fr 0 h0SX h0T h0t h0d).trans h0
  rcases ps with _ | ⟨p, ps'⟩
  · -- `ps = []`
    have hhead : (s1.stk SX).headD HvdH.Glyph.eos ≠ HvdH.Glyph.cons := by
      rw [h1SX]
      simp only [HvdH.encs, List.map_nil, List.flatten_nil, List.nil_append]
      exact gMark_ne_cons
    obtain ⟨s2, n2, h2ev, hn2, h2SX, h2SA, h20, h2t, h2d, h2fr⟩ :=
      merge_updSizeSkip (main := main) (pSize := pSize) (S := SX) (SA := SA) (t := t) (d := d)
        (g := s1.reg) (X := s1.stk) hhead
    have h2SY : s2.stk SY = X SY := (h2fr SY hSYSX hSYSA hSY0 hSYt hSYd).trans h1SY
    have h2Tv : s2.stk T = (HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v').enc ++ Tc :=
      (h2fr T hTSX hTSA hT0 hTt hTd).trans h1T
    have h2SB : s2.stk SB = X SB := (h2fr SB hSBSX hSBSA hSB0 hSBt hSBd).trans h1SB
    have h2F1 : s2.stk F1 = X F1 := (h2fr F1 hF1SX hF1SA hF10 hF1t hF1d).trans h1F1
    have h2F2 : s2.stk F2 = X F2 := (h2fr F2 hF2SX hF2SA hF20 hF2t hF2d).trans h1F2
    refine ⟨s2, n1 + n2, Ev.seqs_cons h1ev h2ev, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [↓reduceIte]; omega
    · exact h2SX.trans h1SX
    · exact h2SY
    · exact h2Tv
    · exact h20.trans h10
    · simp only [↓reduceIte]; exact h2SA.trans h1SA
    · exact h2SB
    · exact h2F1
    · exact h2F2
    · exact h2t.trans h1t
    · exact h2d.trans h1d
    · intro k' hk
      have hkSX : k' ≠ SX := fun he => hk (by simp [he])
      have hkSA : k' ≠ SA := fun he => hk (by simp [he])
      have hk0 : k' ≠ 0 := fun he => hk (by simp [he])
      have hkT : k' ≠ T := fun he => hk (by simp [he])
      have hkt : k' ≠ t := fun he => hk (by simp [he])
      have hkd : k' ≠ d := fun he => hk (by simp [he])
      rw [h2fr k' hkSX hkSA hk0 hkt hkd, h1fr k' hkSX hkT hkt hkd]
  · -- `ps = p :: ps'`
    obtain ⟨k', v'', hp⟩ := hps p (by simp)
    have hS1 : s1.stk SX = (HvdH.Val.cons (HvdH.Val.int (k' : ℤ)) v'').enc ++ (HvdH.encs ps' ++ gMark :: A) := by
      rw [h1SX, hp]
      simp only [HvdH.encs, List.map_cons, List.flatten_cons, List.append_assoc]
    obtain ⟨s2, n2, h2ev, hn2, h2SX, h2SA, h20, h2t, h2d, h2fr⟩ :=
      mrgUpdSize (main := main) (pSize := pSize) (KSz := KSz) hSz
        (S := SX) (SA := SA) (t := t) (d := d) hSXSA hSX0 hSXt hSXd hSA0 hSAt hSAd h0t h0d htd
        (g := s1.reg) (X := s1.stk) (k := k') (v' := v'')
        (A := HvdH.encs ps' ++ gMark :: A) (Sc := X SA) hS1 h1SA
    have hkey : keyOf ((p :: ps').headD HvdH.Val.nil) = k' := by
      rw [List.headD_cons, hp, keyOf_record]
    have h2SY : s2.stk SY = X SY := (h2fr SY hSYSX hSYSA hSY0 hSYt hSYd).trans h1SY
    have h2Tv : s2.stk T = (HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v').enc ++ Tc :=
      (h2fr T hTSX hTSA hT0 hTt hTd).trans h1T
    have h2SB : s2.stk SB = X SB := (h2fr SB hSBSX hSBSA hSB0 hSBt hSBd).trans h1SB
    have h2F1 : s2.stk F1 = X F1 := (h2fr F1 hF1SX hF1SA hF10 hF1t hF1d).trans h1F1
    have h2F2 : s2.stk F2 = X F2 := (h2fr F2 hF2SX hF2SA hF20 hF2t hF2d).trans h1F2
    refine ⟨s2, n1 + n2, Ev.seqs_cons h1ev h2ev, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg (List.cons_ne_nil p ps')]
      have hn2' : n2 ≤ updSizeCost KSz (keyOf ((p :: ps').headD HvdH.Val.nil)) := by
        rw [updSizeCost, pushSizeCost, hkey]
        omega
      omega
    · exact h2SX.trans h1SX
    · exact h2SY
    · exact h2Tv
    · exact h20.trans h10
    · rw [if_neg (List.cons_ne_nil p ps'), hkey]
      exact h2SA
    · exact h2SB
    · exact h2F1
    · exact h2F2
    · exact h2t.trans h1t
    · exact h2d.trans h1d
    · intro k' hk
      have hkSX : k' ≠ SX := fun he => hk (by simp [he])
      have hkSA : k' ≠ SA := fun he => hk (by simp [he])
      have hk0 : k' ≠ 0 := fun he => hk (by simp [he])
      have hkT : k' ≠ T := fun he => hk (by simp [he])
      have hkt : k' ≠ t := fun he => hk (by simp [he])
      have hkd : k' ≠ d := fun he => hk (by simp [he])
      rw [h2fr k' hkSX hkSA hk0 hkt hkd, h1fr k' hkSX hkT hkt hkd]

end Work.Layout
