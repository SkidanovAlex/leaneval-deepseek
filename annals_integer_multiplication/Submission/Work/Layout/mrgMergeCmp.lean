import Mathlib
import Submission.Work.Layout.mrgDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# `Work.Layout.mrgMergeCmp`

The comparison phase of `Sk.mergeStep`: given the two run stacks `SX`, `SY` whose fronts have
already been stripped of their leading `Glyph.cons` (so that `SX` starts with
`(Val.int k).enc ++ v'.enc ++ ...`), the seven commands

`dupInt SX 0 t d, dupInt SY 0 t d, pLt, mvVal 0 F2 t d, readFlag F2 rG,
 pushConst SX Glyph.cons, pushConst SY Glyph.cons`

copy the two keys onto the value stack, compare them (`rG` records whether the key `l` of `SY`
is strictly smaller than the key `k` of `SX`), and re-assemble the two records by pushing the
`cons` tags back.  Everything else — stack `0` (below the two copied keys), `T`, `SA`, `SB`,
`F1`, `t`, `d` and all untouched stacks — is restored.
-/

namespace Work.Layout

open HvdH Work.Layout

/-- `a ∉ l` and `b ∈ l` give `a ≠ b` -/
private theorem ne_of_notMem' {α : Type} [DecidableEq α] {a b : α} {l : List α}
    (h : a ∉ l) (hb : b ∈ l) : a ≠ b := fun hab => h (hab ▸ hb)

private theorem encs_single' (v : Val) : encs [v] = v.enc := by simp [encs]

theorem mrgMergeCmp {main pLt : HvdH.Cmd} {KLt : ℕ}
    (hLt : ∀ main : HvdH.Cmd, HvdH.BinOp main pLt (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => KLt * (HvdH.isz a + HvdH.isz b)))
    {SX SY T SA SB F1 F2 t d : HvdH.Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List HvdH.Stk).Nodup)
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph} {k l : ℕ} {v' w' : HvdH.Val} {ps qs : List HvdH.Val}
    {A B' R : List HvdH.Glyph}
    (hSX : X SX = (HvdH.Val.int (k : ℤ)).enc ++ (v'.enc ++ (HvdH.encs ps ++ Work.Layout.gMark :: A)))
    (hSY : X SY = (HvdH.Val.int (l : ℤ)).enc ++ (w'.enc ++ (HvdH.encs qs ++ Work.Layout.gMark :: B')))
    (h0 : X 0 = R) :
    ∃ s' n, Work.Layout.Ev main (seqs [ Work.Layout.Sk.dupInt SX 0 t d, Work.Layout.Sk.dupInt SY 0 t d, pLt, Work.Layout.mvVal 0 F2 t d,
        Work.Layout.Sk.readFlag F2 Work.Layout.Sk.rG, Work.Layout.pushConst SX HvdH.Glyph.cons, Work.Layout.pushConst SY HvdH.Glyph.cons ]) ⟨g, X⟩ s' n ∧
      n ≤ 40 * (HvdH.isz (k : ℤ) + 1) + 40 * (HvdH.isz (l : ℤ) + 1)
            + KLt * (HvdH.isz (l : ℤ) + HvdH.isz (k : ℤ)) + 64 + 6 + 4 ∧
      s'.stk SX = (HvdH.Val.cons (HvdH.Val.int (k : ℤ)) v').enc ++ HvdH.encs ps ++ Work.Layout.gMark :: A ∧
      s'.stk SY = (HvdH.Val.cons (HvdH.Val.int (l : ℤ)) w').enc ++ HvdH.encs qs ++ Work.Layout.gMark :: B' ∧
      s'.stk 0 = R ∧ s'.stk T = X T ∧ s'.stk SA = X SA ∧ s'.stk SB = X SB ∧
      s'.stk F1 = X F1 ∧ s'.stk F2 = X F2 ∧ s'.stk t = X t ∧ s'.stk d = X d ∧
      s'.reg Work.Layout.Sk.rG = (if l < k then HvdH.Glyph.bit true else HvdH.Glyph.iend) ∧
      (∀ k' : HvdH.Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset HvdH.Stk) → s'.stk k' = X k') := by
  -- ## peel the pairwise distinctness of the ten stacks
  rw [List.nodup_cons] at hdis; obtain ⟨hd1, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨hd2, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨hd3, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨hd4, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨hd5, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨hd6, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨hd7, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨hd8, hdis⟩ := hdis
  rw [List.nodup_cons] at hdis; obtain ⟨hd9, hdis⟩ := hdis
  -- ## the inequalities between the ten stacks
  have hSX0 : SX ≠ 0 := ne_of_notMem' hd1 (by simp)
  have hSXt : SX ≠ t := ne_of_notMem' hd1 (by simp)
  have hSXd : SX ≠ d := ne_of_notMem' hd1 (by simp)
  have hSXSY : SX ≠ SY := ne_of_notMem' hd1 (by simp)
  have hSXT : SX ≠ T := ne_of_notMem' hd1 (by simp)
  have hSXSA : SX ≠ SA := ne_of_notMem' hd1 (by simp)
  have hSXSB : SX ≠ SB := ne_of_notMem' hd1 (by simp)
  have hSXF1 : SX ≠ F1 := ne_of_notMem' hd1 (by simp)
  have hSXF2 : SX ≠ F2 := ne_of_notMem' hd1 (by simp)
  have hSY0 : SY ≠ 0 := ne_of_notMem' hd2 (by simp)
  have hSYt : SY ≠ t := ne_of_notMem' hd2 (by simp)
  have hSYd : SY ≠ d := ne_of_notMem' hd2 (by simp)
  have hSYT : SY ≠ T := ne_of_notMem' hd2 (by simp)
  have hSYSA : SY ≠ SA := ne_of_notMem' hd2 (by simp)
  have hSYSB : SY ≠ SB := ne_of_notMem' hd2 (by simp)
  have hSYF1 : SY ≠ F1 := ne_of_notMem' hd2 (by simp)
  have hSYF2 : SY ≠ F2 := ne_of_notMem' hd2 (by simp)
  have hT0 : T ≠ 0 := ne_of_notMem' hd3 (by simp)
  have hTt : T ≠ t := ne_of_notMem' hd3 (by simp)
  have hTd : T ≠ d := ne_of_notMem' hd3 (by simp)
  have hTF2 : T ≠ F2 := ne_of_notMem' hd3 (by simp)
  have hSA0 : SA ≠ 0 := ne_of_notMem' hd4 (by simp)
  have hSAt : SA ≠ t := ne_of_notMem' hd4 (by simp)
  have hSAd : SA ≠ d := ne_of_notMem' hd4 (by simp)
  have hSAF2 : SA ≠ F2 := ne_of_notMem' hd4 (by simp)
  have hSB0 : SB ≠ 0 := ne_of_notMem' hd5 (by simp)
  have hSBt : SB ≠ t := ne_of_notMem' hd5 (by simp)
  have hSBd : SB ≠ d := ne_of_notMem' hd5 (by simp)
  have hSBF2 : SB ≠ F2 := ne_of_notMem' hd5 (by simp)
  have hF10 : F1 ≠ 0 := ne_of_notMem' hd6 (by simp)
  have hF1t : F1 ≠ t := ne_of_notMem' hd6 (by simp)
  have hF1d : F1 ≠ d := ne_of_notMem' hd6 (by simp)
  have hF1F2 : F1 ≠ F2 := ne_of_notMem' hd6 (by simp)
  have hF20 : F2 ≠ 0 := ne_of_notMem' hd7 (by simp)
  have hF2t : F2 ≠ t := ne_of_notMem' hd7 (by simp)
  have hF2d : F2 ≠ d := ne_of_notMem' hd7 (by simp)
  have ht0 : t ≠ 0 := ne_of_notMem' hd8 (by simp)
  have htd : t ≠ d := ne_of_notMem' hd8 (by simp)
  have hd0 : d ≠ 0 := ne_of_notMem' hd9 (by simp)
  -- ## step 1: `dupInt SX 0 t d`
  obtain ⟨s1, n1, e1, hn1, h1SX, h1_0, h1t, h1d, h1fr⟩ :=
    dupInt_ev (main := main) (S := SX) (B := 0) (T := t) (d := d)
      hSX0 hSXt hSXd ht0.symm hd0.symm htd (g := g) (X := X) (z := (k : ℤ)) hSX
  have hn1' : n1 ≤ 40 * (isz (k : ℤ) + 1) := by rw [vsz_int] at hn1; exact hn1
  have h1SY : s1.stk SY = X SY := h1fr SY hSXSY.symm hSY0 hSYt hSYd
  -- ## step 2: `dupInt SY 0 t d`
  obtain ⟨s2, n2, e2, hn2, h2SY, h2_0, h2t, h2d, h2fr⟩ :=
    dupInt_ev (main := main) (S := SY) (B := 0) (T := t) (d := d)
      hSY0 hSYt hSYd ht0.symm hd0.symm htd (g := s1.reg) (X := s1.stk) (z := (l : ℤ))
      (A := w'.enc ++ (encs qs ++ Work.Layout.gMark :: B'))
      (by rw [h1SY]; exact hSY)
  have hn2' : n2 ≤ 40 * (isz (l : ℤ) + 1) := by rw [vsz_int] at hn2; exact hn2
  -- ## step 3: `pLt`, comparing the two keys
  have h20 : s2.stk 0 = encs [Val.int (l : ℤ), Val.int (k : ℤ)] ++ X 0 := by
    rw [h2_0, h1_0, h0, encs_two]
  obtain ⟨out3, s3, n3, hpost3, e3, hn3, h30, h3fr⟩ :=
    (hLt main) [Val.int (l : ℤ), Val.int (k : ℤ)] ⟨(l : ℤ), (k : ℤ), [], rfl, trivial⟩
      s2 (X 0) h20
  have hn3' : n3 ≤ KLt * (isz (l : ℤ) + isz (k : ℤ)) := by
    simpa [binCost] using hn3
  have e3' : Ev main pLt s2 s3 n3 := ⟨n3, e3, le_rfl⟩
  obtain ⟨a3, b3, r3, hv3, hout3⟩ := hpost3
  obtain ⟨ha3, hrest3⟩ := List.cons.inj hv3
  obtain ⟨hb3, hr3⟩ := List.cons.inj hrest3
  have hra3 : a3 = (l : ℤ) := (Val.int.inj ha3).symm
  have hrb3 : b3 = (k : ℤ) := (Val.int.inj hb3).symm
  have hrr3 : r3 = [] := hr3.symm
  have hout3' : out3 = [Val.int (if (l : ℤ) < (k : ℤ) then 1 else 0)] := by
    rw [hout3, hra3, hrb3, hrr3]
  have h30' : s3.stk 0 = (Val.int (if (l : ℤ) < (k : ℤ) then 1 else 0)).enc ++ X 0 := by
    rw [h30, hout3', encs_single']
  -- ## step 4: `mvVal 0 F2 t d`, moving the comparison result to `F2`
  have h3F2 : s3.stk F2 = X F2 := by
    rw [h3fr F2 hF20, h2fr F2 hSYF2.symm hF20 hF2t hF2d, h1fr F2 hSXF2.symm hF20 hF2t hF2d]
  obtain ⟨s4, n4, e4, hn4, h40, h4F2, h4t, h4d, h4fr⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := F2) (c := t) (d := d)
      hF20.symm ht0.symm hd0.symm hF2t hF2d htd (g := s3.reg) (X := s3.stk)
      (v := Val.int (if (l : ℤ) < (k : ℤ) then 1 else 0)) (A := X 0) (B := X F2) h30' h3F2
  have hflag_le : vsz (Val.int (if (l : ℤ) < (k : ℤ) then 1 else 0)) ≤ 3 := by
    rw [vsz_int]
    by_cases h : (l : ℤ) < (k : ℤ) <;> simp [isz, h]
  have hn4' : n4 ≤ 64 := by omega
  -- ## step 5: `readFlag F2 rG`, recording the comparison in the register
  obtain ⟨s5, n5, e5, hn5, h5F2, h5rG, h5fr⟩ :=
    merge_readFlag (main := main) (f := F2) (r := Sk.rG) (by decide) (g := s4.reg) (X := s4.stk)
      (b := decide ((l : ℤ) < (k : ℤ))) (G := X F2)
      (by
        rw [h4F2]
        congr 1
        by_cases h : (l : ℤ) < (k : ℤ) <;> simp [h])
  have h5rG' : s5.reg Sk.rG = (if l < k then Glyph.bit true else Glyph.iend) := by
    rw [h5rG]
    by_cases h : l < k <;> simp [h]
  -- ## step 6: re-assemble the record on `SX`
  obtain ⟨s6, n6, e6, hn6, h6SX, h6fr, h6rB, h6reg⟩ :=
    pushConst_ev (main := main) (k := SX) (cst := Glyph.cons) (g := s5.reg) (X := s5.stk)
  -- ## step 7: re-assemble the record on `SY`
  obtain ⟨s7, n7, e7, hn7, h7SY, h7fr, h7rB, h7reg⟩ :=
    pushConst_ev (main := main) (k := SY) (cst := Glyph.cons) (g := s6.reg) (X := s6.stk)
  -- ## the composite evaluation
  have h67 : Ev main (seqs [pushConst SX Glyph.cons, pushConst SY Glyph.cons]) s5 s7 (n6 + n7) :=
    Ev.seq e6 e7
  have h567 : Ev main (seqs [Sk.readFlag F2 Sk.rG, pushConst SX Glyph.cons,
      pushConst SY Glyph.cons]) s4 s7 (n5 + (n6 + n7)) := Ev.seqs_cons e5 h67
  have h4567 : Ev main (seqs [mvVal 0 F2 t d, Sk.readFlag F2 Sk.rG, pushConst SX Glyph.cons,
      pushConst SY Glyph.cons]) s3 s7 (n4 + (n5 + (n6 + n7))) := Ev.seqs_cons e4 h567
  have h34567 : Ev main (seqs [pLt, mvVal 0 F2 t d, Sk.readFlag F2 Sk.rG,
      pushConst SX Glyph.cons, pushConst SY Glyph.cons]) s2 s7 (n3 + (n4 + (n5 + (n6 + n7)))) :=
    Ev.seqs_cons e3' h4567
  have h234567 : Ev main (seqs [Sk.dupInt SY 0 t d, pLt, mvVal 0 F2 t d, Sk.readFlag F2 Sk.rG,
      pushConst SX Glyph.cons, pushConst SY Glyph.cons]) s1 s7
      (n2 + (n3 + (n4 + (n5 + (n6 + n7))))) := Ev.seqs_cons e2 h34567
  have hmain : Ev main (seqs [Sk.dupInt SX 0 t d, Sk.dupInt SY 0 t d, pLt, mvVal 0 F2 t d,
      Sk.readFlag F2 Sk.rG, pushConst SX Glyph.cons, pushConst SY Glyph.cons]) ⟨g, X⟩ s7
      (n1 + (n2 + (n3 + (n4 + (n5 + (n6 + n7)))))) := Ev.seqs_cons e1 h234567
  -- ## the cost bound
  have hcost : n1 + (n2 + (n3 + (n4 + (n5 + (n6 + n7))))) ≤
      40 * (isz (k : ℤ) + 1) + 40 * (isz (l : ℤ) + 1)
        + KLt * (isz (l : ℤ) + isz (k : ℤ)) + 64 + 6 + 4 := by
    have h6 : n6 ≤ 2 := hn6
    have h7 : n7 ≤ 2 := hn7
    omega
  -- ## the values on `SX` and `SY`
  have hSXfin : s7.stk SX = (Val.cons (Val.int (k : ℤ)) v').enc ++ encs ps ++ gMark :: A := by
    rw [h7fr SX hSXSY, h6SX, h5fr SX hSXF2, h4fr SX hSX0 hSXF2 hSXt hSXd, h3fr SX hSX0,
      h2fr SX hSXSY hSX0 hSXt hSXd, h1SX, hSX, record_cons_recomp]
  have hSYfin : s7.stk SY = (Val.cons (Val.int (l : ℤ)) w').enc ++ encs qs ++ gMark :: B' := by
    rw [h7SY, h6fr SY hSXSY.symm, h5fr SY hSYF2, h4fr SY hSY0 hSYF2 hSYt hSYd, h3fr SY hSY0,
      h2SY, h1fr SY hSXSY.symm hSY0 hSYt hSYd, hSY, record_cons_recomp]
  -- ## the restored stacks
  have h0fin : s7.stk 0 = R := by
    rw [h7fr 0 hSY0.symm, h6fr 0 hSX0.symm, h5fr 0 hF20.symm, h40, h0]
  have hTfin : s7.stk T = X T := by
    rw [h7fr T hSYT.symm, h6fr T hSXT.symm, h5fr T hTF2, h4fr T hT0 hTF2 hTt hTd,
      h3fr T hT0, h2fr T hSYT.symm hT0 hTt hTd, h1fr T hSXT.symm hT0 hTt hTd]
  have hSAfin : s7.stk SA = X SA := by
    rw [h7fr SA hSYSA.symm, h6fr SA hSXSA.symm, h5fr SA hSAF2, h4fr SA hSA0 hSAF2 hSAt hSAd,
      h3fr SA hSA0, h2fr SA hSYSA.symm hSA0 hSAt hSAd, h1fr SA hSXSA.symm hSA0 hSAt hSAd]
  have hSBfin : s7.stk SB = X SB := by
    rw [h7fr SB hSYSB.symm, h6fr SB hSXSB.symm, h5fr SB hSBF2, h4fr SB hSB0 hSBF2 hSBt hSBd,
      h3fr SB hSB0, h2fr SB hSYSB.symm hSB0 hSBt hSBd, h1fr SB hSXSB.symm hSB0 hSBt hSBd]
  have hF1fin : s7.stk F1 = X F1 := by
    rw [h7fr F1 hSYF1.symm, h6fr F1 hSXF1.symm, h5fr F1 hF1F2, h4fr F1 hF10 hF1F2 hF1t hF1d,
      h3fr F1 hF10, h2fr F1 hSYF1.symm hF10 hF1t hF1d, h1fr F1 hSXF1.symm hF10 hF1t hF1d]
  have hF2fin : s7.stk F2 = X F2 := by
    rw [h7fr F2 hSYF2.symm, h6fr F2 hSXF2.symm, h5F2]
  have htfin : s7.stk t = X t := by
    rw [h7fr t hSYt.symm, h6fr t hSXt.symm, h5fr t hF2t.symm, h4t, h3fr t ht0, h2t, h1t]
  have hdfin : s7.stk d = X d := by
    rw [h7fr d hSYd.symm, h6fr d hSXd.symm, h5fr d hF2d.symm, h4d, h3fr d hd0, h2d, h1d]
  -- ## the register `rG`
  have hrGfin : s7.reg Sk.rG = (if l < k then Glyph.bit true else Glyph.iend) := by
    rw [h7reg Sk.rG (by decide), h6reg Sk.rG (by decide), h5rG']
  -- ## the frame
  have hfrfin : ∀ k' : HvdH.Stk, k' ∉ ({SX, SY, SA, SB, T, F1, F2, t, d, 0} : Finset HvdH.Stk) →
      s7.stk k' = X k' := by
    intro k' hk'
    obtain ⟨hkSX, hkSY, hkSA, hkSB, hkT, hkF1, hkF2, hkt, hkd, hk0⟩ :
        k' ≠ SX ∧ k' ≠ SY ∧ k' ≠ SA ∧ k' ≠ SB ∧ k' ≠ T ∧ k' ≠ F1 ∧ k' ≠ F2 ∧
          k' ≠ t ∧ k' ≠ d ∧ k' ≠ 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
      exact hk'
    rw [h7fr k' hkSY, h6fr k' hkSX, h5fr k' hkF2, h4fr k' hk0 hkF2 hkt hkd, h3fr k' hk0,
      h2fr k' hkSY hk0 hkt hkd, h1fr k' hkSX hk0 hkt hkd]
  exact ⟨s7, _, hmain, hcost, hSXfin, hSYfin, h0fin, hTfin, hSAfin, hSBfin, hF1fin, hF2fin,
    htfin, hdfin, hrGfin, hfrfin⟩

end Work.Layout
