import Mathlib
import Submission.Work.Layout.mrgDefs
import Submission.Work.Layout.mrgUpdSize
import Submission.Work.Layout.merge_updSizeSkip

namespace Work.Layout

open HvdH Work.Layout

/-!
# The second move of `Sk.mergeStep` on the `SY` side

This is the "move the head record of `SY` onto `T`, then refresh the cached size on `SB`" phase of
`Sk.mergeStep` (the branch taken when the run of `SY` is nonempty and its front key is not larger).
It is used in the assembly of `Work.Layout.mrgMergeStep`.

The two commands are `mvVal SY T t d` (which moves the record `Val.cons (Val.int l) w'` from `SY`
onto `T`, exposing what lies below it) followed by `Sk.updSize pSize SY SB t d` (which, if a record
is still exposed on `SY`, pushes the *bit size* of its key onto `SB`; if not, it does nothing).

The proof is by cases on `qs`:

* `qs = []`: after the move, `SY` carries only the frame marker `gMark`, so `updSize` degenerates to
  `skip` (`merge_updSizeSkip`) and `SB` is unchanged;
* `qs = q :: qs`: after the move, `SY` carries the record `q = Val.cons (Val.int k') v''`, so
  `mrgUpdSize` applies and pushes `(keyOf q).size = k'.size` onto `SB`.
-/

/-- the 45 pairwise distinctness facts contained in the `Nodup` hypothesis on the ten stacks -/
private theorem mrgNodup10 {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    SX ≠ SY ∧ SX ≠ T ∧ SX ≠ SA ∧ SX ≠ SB ∧ SX ≠ F1 ∧ SX ≠ F2 ∧ SX ≠ t ∧ SX ≠ d ∧ SX ≠ 0 ∧
    SY ≠ T ∧ SY ≠ SA ∧ SY ≠ SB ∧ SY ≠ F1 ∧ SY ≠ F2 ∧ SY ≠ t ∧ SY ≠ d ∧ SY ≠ 0 ∧
    T ≠ SA ∧ T ≠ SB ∧ T ≠ F1 ∧ T ≠ F2 ∧ T ≠ t ∧ T ≠ d ∧ T ≠ 0 ∧
    SA ≠ SB ∧ SA ≠ F1 ∧ SA ≠ F2 ∧ SA ≠ t ∧ SA ≠ d ∧ SA ≠ 0 ∧
    SB ≠ F1 ∧ SB ≠ F2 ∧ SB ≠ t ∧ SB ≠ d ∧ SB ≠ 0 ∧
    F1 ≠ F2 ∧ F1 ≠ t ∧ F1 ≠ d ∧ F1 ≠ 0 ∧
    F2 ≠ t ∧ F2 ≠ d ∧ F2 ≠ 0 ∧
    t ≠ d ∧ t ≠ 0 ∧ d ≠ 0 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    (intro h; rw [h] at hdis; simp at hdis)

/-- the two-element `seqs` composition -/
private theorem Ev.seqs_pair {main : Cmd} {p q : Cmd} {s t u : State} {C1 C2 : ℕ}
    (h1 : Ev main p s t C1) (h2 : Ev main q t u C2) :
    Ev main (seqs [p, q]) s u (C1 + C2) := by
  simpa [seqs] using Ev.seq h1 h2

theorem mrgMergeMoveQ2 {main pSize : HvdH.Cmd} {KSz : ℕ}
    (hSz : ∀ main : HvdH.Cmd, HvdH.UnOp main pSize (fun _ => True) (fun a => (a.natAbs.size : ℤ))
      (fun a => KSz * HvdH.isz a))
    {SX SY T SA SB F1 F2 t d : HvdH.Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List HvdH.Stk).Nodup)
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph} {k l : ℕ} {v' w' : HvdH.Val} {ps qs : List HvdH.Val}
    {A B' Tc R : List HvdH.Glyph}
    (hqs : ∀ v ∈ qs, ∃ (k' : ℕ) (v'' : HvdH.Val), v = HvdH.Val.cons (HvdH.Val.int (k' : ℤ)) v'')
    (hSX : X SX = (HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v').enc ++ HvdH.encs ps ++ Work.Layout.gMark :: A)
    (hSY : X SY = (HvdH.Val.cons (HvdH.Val.int (l : ℤ)) w').enc ++ HvdH.encs qs ++ Work.Layout.gMark :: B')
    (hT : X T = Tc) (h0 : X 0 = R) :
    ∃ s' n, Work.Layout.Ev main (seqs [ Work.Layout.mvVal SY T t d, Work.Layout.Sk.updSize pSize SY SB t d ]) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (HvdH.vsz (HvdH.Val.cons (HvdH.Val.int (l : ℤ)) w') + 1)
            + (if qs = [] then 4 else Work.Layout.updSizeCost KSz (Work.Layout.keyOf (qs.headD HvdH.Val.nil))) ∧
      s'.stk SX = X SX ∧
      s'.stk SY = HvdH.encs qs ++ Work.Layout.gMark :: B' ∧
      s'.stk T = (HvdH.Val.cons (HvdH.Val.int (l : ℤ)) w').enc ++ Tc ∧
      s'.stk 0 = R ∧ s'.stk SA = X SA ∧
      s'.stk SB = (if qs = [] then X SB
                   else (HvdH.Val.int ((Work.Layout.keyOf (qs.headD HvdH.Val.nil)).size : ℤ)).enc ++ X SB) ∧
      s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      (∀ k' : HvdH.Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset HvdH.Stk) → s'.stk k' = X k') := by
  obtain ⟨hSX_SY, hSX_T, hSX_SA, hSX_SB, hSX_F1, hSX_F2, hSX_t, hSX_d, hSX_0,
          hSY_T, hSY_SA, hSY_SB, hSY_F1, hSY_F2, hSY_t, hSY_d, hSY_0,
          hT_SA, hT_SB, hT_F1, hT_F2, hT_t, hT_d, hT_0,
          hSA_SB, hSA_F1, hSA_F2, hSA_t, hSA_d, hSA_0,
          hSB_F1, hSB_F2, hSB_t, hSB_d, hSB_0,
          hF1_F2, hF1_t, hF1_d, hF1_0,
          hF2_t, hF2_d, hF2_0, ht_d, ht_0, hd_0⟩ := mrgNodup10 hdis
  cases qs with
  | nil =>
      -- after the move, `SY` is empty: `updSize` is a no-op
      have hSY' : X SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ (gMark :: B') := by
        simpa [encs] using hSY
      obtain ⟨s1, n1, e1, hn1, h1SY, h1T, h1t, h1d, h1fr⟩ :=
        mvVal_ev_full (main := main) (a := SY) (b := T) (c := t) (d := d)
          hSY_T hSY_t hSY_d hT_t hT_d ht_d (g := g) (X := X)
          (v := Val.cons (Val.int (l : ℤ)) w') (A := gMark :: B') (B := Tc) hSY' hT
      have hhead : (s1.stk SY).headD Glyph.eos ≠ Glyph.cons := by
        rw [h1SY]; exact gMark_ne_cons
      obtain ⟨s2, n2, e2, hn2, h2SY, h2SB, h20, h2t, h2d, h2fr⟩ :=
        merge_updSizeSkip (main := main) (pSize := pSize) (S := SY) (SA := SB) (t := t) (d := d)
          (g := s1.reg) (X := s1.stk) hhead
      have he : Ev main (seqs [mvVal SY T t d, Sk.updSize pSize SY SB t d]) ⟨g, X⟩ s2 (n1 + n2) :=
        Ev.seqs_pair e1 e2
      refine ⟨s2, n1 + n2, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [ite_true]; omega
      · rw [h2fr SX hSX_SY hSX_SB hSX_0 hSX_t hSX_d, h1fr SX hSX_SY hSX_T hSX_t hSX_d]
      · rw [h2SY, h1SY]; simp [encs]
      · rw [h2fr T hSY_T.symm hT_SB hT_0 hT_t hT_d, h1T]
      · rw [h20, h1fr 0 hSY_0.symm hT_0.symm ht_0.symm hd_0.symm, h0]
      · rw [h2fr SA hSY_SA.symm hSA_SB hSA_0 hSA_t hSA_d, h1fr SA hSY_SA.symm hT_SA.symm hSA_t hSA_d]
      · rw [h2SB, h1fr SB hSY_SB.symm hT_SB.symm hSB_t hSB_d]; simp only [ite_true]
      · rw [h2fr F1 hSY_F1.symm hSB_F1.symm hF1_0 hF1_t hF1_d, h1fr F1 hSY_F1.symm hT_F1.symm hF1_t hF1_d]
      · rw [h2fr F2 hSY_F2.symm hSB_F2.symm hF2_0 hF2_t hF2_d, h1fr F2 hSY_F2.symm hT_F2.symm hF2_t hF2_d]
      · rw [h2t, h1t]
      · rw [h2d, h1d]
      · intro k' hk
        have e1 : k' ≠ SY := fun h => hk (by simp [h])
        have e2 : k' ≠ SB := fun h => hk (by simp [h])
        have e3 : k' ≠ 0 := fun h => hk (by simp [h])
        have e4 : k' ≠ t := fun h => hk (by simp [h])
        have e5 : k' ≠ d := fun h => hk (by simp [h])
        have e6 : k' ≠ T := fun h => hk (by simp [h])
        rw [h2fr k' e1 e2 e3 e4 e5, h1fr k' e1 e6 e4 e5]
  | cons q qs =>
      -- after the move, `SY` carries the record `q`: refresh `SB` with its key size
      rw [List.append_assoc] at hSY
      obtain ⟨k', v'', hq0, hkeyq⟩ := headD_record (l := q :: qs) hqs (by simp)
      have hq : q = Val.cons (Val.int (k' : ℤ)) v'' := by simpa using hq0
      obtain ⟨s1, n1, e1, hn1, h1SY, h1T, h1t, h1d, h1fr⟩ :=
        mvVal_ev_full (main := main) (a := SY) (b := T) (c := t) (d := d)
          hSY_T hSY_t hSY_d hT_t hT_d ht_d (g := g) (X := X)
          (v := Val.cons (Val.int (l : ℤ)) w') (A := encs (q :: qs) ++ gMark :: B') (B := Tc) hSY hT
      have hS : s1.stk SY = (Val.cons (Val.int (k' : ℤ)) v'').enc ++ (encs qs ++ gMark :: B') := by
        rw [h1SY, ← hq]; simp [encs, List.append_assoc]
      have hSB1 : s1.stk SB = X SB := h1fr SB hSY_SB.symm hT_SB.symm hSB_t hSB_d
      obtain ⟨s2, n2, e2, hn2, h2S, h2SA, h20, h2t, h2d, h2fr⟩ :=
        mrgUpdSize (main := main) (pSize := pSize) (KSz := KSz) hSz
          hSY_SB hSY_0 hSY_t hSY_d hSB_0 hSB_t hSB_d ht_0.symm hd_0.symm ht_d
          (g := s1.reg) (X := s1.stk) (k := k') (v' := v'') (A := encs qs ++ gMark :: B') (Sc := X SB)
          hS hSB1
      have he : Ev main (seqs [mvVal SY T t d, Sk.updSize pSize SY SB t d]) ⟨g, X⟩ s2 (n1 + n2) :=
        Ev.seqs_pair e1 e2
      have hif : (if (q :: qs) = [] then 4 else updSizeCost KSz (keyOf ((q :: qs).headD Val.nil)))
          = updSizeCost KSz k' := by
        have hne : (q :: qs) ≠ ([] : List Val) := by simp
        simp only [hne, ite_false, hkeyq]
      refine ⟨s2, n1 + n2, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hif, updSizeCost, pushSizeCost]; omega
      · rw [h2fr SX hSX_SY hSX_SB hSX_0 hSX_t hSX_d, h1fr SX hSX_SY hSX_T hSX_t hSX_d]
      · rw [h2S, h1SY]
      · rw [h2fr T hSY_T.symm hT_SB hT_0 hT_t hT_d, h1T]
      · rw [h20, h1fr 0 hSY_0.symm hT_0.symm ht_0.symm hd_0.symm, h0]
      · rw [h2fr SA hSY_SA.symm hSA_SB hSA_0 hSA_t hSA_d, h1fr SA hSY_SA.symm hT_SA.symm hSA_t hSA_d]
      · have hne : (q :: qs) ≠ ([] : List Val) := by simp
        simp only [hne, ite_false]
        rw [h2SA, hkeyq]
      · rw [h2fr F1 hSY_F1.symm hSB_F1.symm hF1_0 hF1_t hF1_d, h1fr F1 hSY_F1.symm hT_F1.symm hF1_t hF1_d]
      · rw [h2fr F2 hSY_F2.symm hSB_F2.symm hF2_0 hF2_t hF2_d, h1fr F2 hSY_F2.symm hT_F2.symm hF2_t hF2_d]
      · rw [h2t, h1t]
      · rw [h2d, h1d]
      · intro k' hk
        have e1 : k' ≠ SY := fun h => hk (by simp [h])
        have e2 : k' ≠ SB := fun h => hk (by simp [h])
        have e3 : k' ≠ 0 := fun h => hk (by simp [h])
        have e4 : k' ≠ t := fun h => hk (by simp [h])
        have e5 : k' ≠ d := fun h => hk (by simp [h])
        have e6 : k' ≠ T := fun h => hk (by simp [h])
        rw [h2fr k' e1 e2 e3 e4 e5, h1fr k' e1 e6 e4 e5]

end Work.Layout
