import Mathlib
import Submission.Work.SynFFT.zipKit

namespace Work.SynFFT

open HvdH
open Work.Layout

set_option maxHeartbeats 1600000

/-- One iteration of the `zipCat` loop when both groups are nonempty: the body of
`Work.SynFFT.zBody zApp` is (definitionally)

    peek 1 zP; ite zP cons
      ( pop 1 rA; peek 2 zP; ite zP cons
          ( pop 2 rA; mvVal 2 0 4 5; mvVal 1 0 4 5; zMer zApp zF )
          ( pushConst 0 nil; mvVal 1 0 4 5; zMer zApp zF ) )
      ( peek 2 zP; ite zP cons (...) ( set zF eos ) )

with `zMer zApp f = seqs [zApp, prependTo 0 3 4 5 rA, .set f cons]`; here both heads are `cons`.
Useful pieces, all available: `Work.SynFFT.zMer_ev` (the merge gadget), `Work.Layout.ev_peek'`,
`Work.Layout.ev_pop'`, `Work.Layout.mvVal_ev_full` (cost `16 * (vsz v + 1)`),
`Work.Layout.Ev.seq'`, `Work.Layout.Ev.iteT`, `Work.Layout.Ev.iteF`,
`Work.SynFFT.ofList_map_ofList_cons` (the encoding shape of a cons-cell of a group value) and
`Work.SynFFT.zBump_cons`/`zStepCost` for the cost: `zStepCost KA (r1 :: t1) (r2 :: t2)
= (KA + 100) * (vsz (ofList r1) + 1 + (vsz (ofList r2) + 1))`; `omega` closes the arithmetic. -/
theorem zipStepCC {main zApp : HvdH.Cmd} {KA : ℕ}
    (hApp : ∀ (xs ys rest' : List HvdH.Val), HvdH.WordR main zApp
      (fun vs => vs = HvdH.ofList xs :: HvdH.ofList ys :: rest')
      (fun _ out => out = HvdH.ofList (xs ++ ys) :: rest')
      (fun _ => KA * (HvdH.vsz (HvdH.ofList xs) + 1)))
    {rest : List HvdH.Val} {R : List HvdH.Glyph} {r1 r2 : List HvdH.Val}
    {t1 t2 : List (List HvdH.Val)} {Racc : List (List HvdH.Val)} {Z1 Z2 Z3 : List HvdH.Glyph}
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph}
    (h0 : X 0 = HvdH.encs rest ++ R)
    (h1 : X 1 = HvdH.Glyph.cons :: ((HvdH.ofList r1).enc ++
      ((HvdH.ofList (t1.map HvdH.ofList)).enc ++ Z1)))
    (h2 : X 2 = HvdH.Glyph.cons :: ((HvdH.ofList r2).enc ++
      ((HvdH.ofList (t2.map HvdH.ofList)).enc ++ Z2)))
    (h3 : X 3 = (HvdH.ofList (Racc.map HvdH.ofList)).enc ++ Z3) :
    ∃ s' n, Work.Layout.Ev main (Work.SynFFT.zBody zApp) ⟨g, X⟩ s' n ∧
      n ≤ Work.SynFFT.zStepCost KA (r1 :: t1) (r2 :: t2) ∧
      s'.stk 0 = X 0 ∧
      s'.stk 1 = (HvdH.ofList (t1.map HvdH.ofList)).enc ++ Z1 ∧
      s'.stk 2 = (HvdH.ofList (t2.map HvdH.ofList)).enc ++ Z2 ∧
      s'.stk 3 = (HvdH.ofList ((HvdH.ofList (r1 ++ r2)) :: Racc.map HvdH.ofList)).enc ++ Z3 ∧
      s'.reg Work.SynFFT.zF = HvdH.Glyph.cons ∧
      s'.stk 4 = X 4 ∧ s'.stk 5 = X 5 ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 → s'.stk k = X k) := by

  ----------------------------------------------------------------------
  -- The heads of the two groups are `cons` cells, so the encodings split
  -- into a head row and the remaining rows.
  ----------------------------------------------------------------------
  have hhd1 : (X 1).headD Glyph.eos = Glyph.cons := by rw [h1]; rfl
  have hhd2 : (X 2).headD Glyph.eos = Glyph.cons := by rw [h2]; rfl
  have htl1 : (X 1).tail = (ofList r1).enc ++ ((ofList (t1.map ofList)).enc ++ Z1) := by
    rw [h1]; rfl
  have htl2 : (X 2).tail = (ofList r2).enc ++ ((ofList (t2.map ofList)).enc ++ Z2) := by
    rw [h2]; rfl
  ----------------------------------------------------------------------
  -- The command abbreviations of `zBody zApp`
  ----------------------------------------------------------------------
  let B1T : Cmd := seqs [.pop 2 rA, mvVal 2 0 4 5, mvVal 1 0 4 5, zMer zApp zF]
  let B1F : Cmd := seqs [pushConst 0 Glyph.nil, mvVal 1 0 4 5, zMer zApp zF]
  let ITE2 : Cmd := .ite zP Glyph.cons B1T B1F
  let B1 : Cmd := seqs [.pop 1 rA, .peek 2 zP, ITE2]
  let B2T : Cmd := seqs [pushConst 0 Glyph.nil, .pop 2 rA, mvVal 2 0 4 5, zMer zApp zF]
  let B2F : Cmd := .set zF Glyph.eos
  let B2 : Cmd := seqs [.peek 2 zP, .ite zP Glyph.cons B2T B2F]
  let ITE1 : Cmd := .ite zP Glyph.cons B1 B2
  have hzBody : zBody zApp = seqs [.peek 1 zP, ITE1] := rfl
  ----------------------------------------------------------------------
  -- The four steps `peek 1 zP`, `pop 1 rA`, `peek 2 zP`, `pop 2 rA`
  ----------------------------------------------------------------------
  let gP : Reg → Glyph := Function.update g zP ((X 1).headD Glyph.eos)
  let X1 : Stk → List Glyph := Function.update X 1 (X 1).tail
  let gA : Reg → Glyph := Function.update gP rA ((X 1).headD Glyph.eos)
  let gB : Reg → Glyph := Function.update gA zP ((X1 2).headD Glyph.eos)
  let X2 : Stk → List Glyph := Function.update X1 2 (X1 2).tail
  let gC : Reg → Glyph := Function.update gB rA ((X1 2).headD Glyph.eos)
  have hPeek1 : Ev main (.peek 1 zP) ⟨g, X⟩ ⟨gP, X⟩ 1 := ev_peek' main 1 zP g X
  have hPop1 : Ev main (.pop 1 rA) ⟨gP, X⟩ ⟨gA, X1⟩ 1 := ev_pop' main 1 rA gP X
  have hPeek2 : Ev main (.peek 2 zP) ⟨gA, X1⟩ ⟨gB, X1⟩ 1 := ev_peek' main 2 zP gA X1
  have hPop2 : Ev main (.pop 2 rA) ⟨gB, X1⟩ ⟨gC, X2⟩ 1 := ev_pop' main 2 rA gB X1
  ----------------------------------------------------------------------
  -- What the four intermediate stack functions look like
  ----------------------------------------------------------------------
  have hX1_0 : X1 0 = X 0 := by
    simp only [X1, Function.update_of_ne (by decide : (0 : Stk) ≠ 1)]
  have hX1_1 : X1 1 = (ofList r1).enc ++ ((ofList (t1.map ofList)).enc ++ Z1) := by
    simp only [X1, Function.update_self, htl1]
  have hX1_2 : X1 2 = X 2 := by
    simp only [X1, Function.update_of_ne (by decide : (2 : Stk) ≠ 1)]
  have hX1_3 : X1 3 = X 3 := by
    simp only [X1, Function.update_of_ne (by decide : (3 : Stk) ≠ 1)]
  have hX1_4 : X1 4 = X 4 := by
    simp only [X1, Function.update_of_ne (by decide : (4 : Stk) ≠ 1)]
  have hX1_5 : X1 5 = X 5 := by
    simp only [X1, Function.update_of_ne (by decide : (5 : Stk) ≠ 1)]
  have hX2_0 : X2 0 = X 0 := by
    simp only [X2, Function.update_of_ne (by decide : (0 : Stk) ≠ 2), hX1_0]
  have hX2_1 : X2 1 = X1 1 := by
    simp only [X2, Function.update_of_ne (by decide : (1 : Stk) ≠ 2)]
  have hX2_2 : X2 2 = (ofList r2).enc ++ ((ofList (t2.map ofList)).enc ++ Z2) := by
    simp only [X2, Function.update_self, hX1_2, htl2]
  have hX2_3 : X2 3 = X 3 := by
    simp only [X2, Function.update_of_ne (by decide : (3 : Stk) ≠ 2), hX1_3]
  have hX2_4 : X2 4 = X 4 := by
    simp only [X2, Function.update_of_ne (by decide : (4 : Stk) ≠ 2), hX1_4]
  have hX2_5 : X2 5 = X 5 := by
    simp only [X2, Function.update_of_ne (by decide : (5 : Stk) ≠ 2), hX1_5]
  ----------------------------------------------------------------------
  -- `mvVal 2 0 4 5`: move the head row of group 2 to the value stack
  ----------------------------------------------------------------------
  obtain ⟨s3, n3, hEv3, hn3, hs3_2, hs3_0, hs3_4, hs3_5, hfr3⟩ :=
    mvVal_ev_full (main := main) (a := 2) (b := 0) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := gC) (X := X2) (v := ofList r2)
      (A := (ofList (t2.map ofList)).enc ++ Z2) (B := X2 0) hX2_2 rfl
  ----------------------------------------------------------------------
  -- `mvVal 1 0 4 5`: move the head row of group 1 to the value stack
  ----------------------------------------------------------------------
  have hs3_1 : s3.stk 1 = (ofList r1).enc ++ ((ofList (t1.map ofList)).enc ++ Z1) := by
    rw [hfr3 1 (by decide) (by decide) (by decide) (by decide), hX2_1, hX1_1]
  obtain ⟨s4, n4, hEv4, hn4, hs4_1, hs4_0, hs4_4, hs4_5, hfr4⟩ :=
    mvVal_ev_full (main := main) (a := 1) (b := 0) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s3.reg) (X := s3.stk) (v := ofList r1)
      (A := (ofList (t1.map ofList)).enc ++ Z1) (B := s3.stk 0) hs3_1 rfl
  ----------------------------------------------------------------------
  -- `zMer zApp zF`: merge the two head rows, prepend, and continue
  ----------------------------------------------------------------------
  have hs4_0' : s4.stk 0 = encs (ofList r1 :: ofList r2 :: rest) ++ R := by
    rw [hs4_0, hs3_0, hX2_0, h0]
    simp only [Work.Kernel.encs_cons, List.append_assoc]
  have hs4_3 : s4.stk 3 = (ofList (Racc.map ofList)).enc ++ Z3 := by
    rw [hfr4 3 (by decide) (by decide) (by decide) (by decide),
        hfr3 3 (by decide) (by decide) (by decide) (by decide), hX2_3, h3]
  obtain ⟨s5, n5, hEv5, hn5, hs5_0, hs5_3, hs5_reg, hs5_4, hs5_5, hfr5⟩ :=
    zMer_ev (main := main) (zApp := zApp) (KA := KA) (f := zF) hApp
      (rest := rest) (R := R) (r₁ := r1) (r₂ := r2) (Racc := Racc) (Z3 := Z3)
      (g := s4.reg) (X := s4.stk) hs4_0' hs4_3
  ----------------------------------------------------------------------
  -- Assemble the evaluation of `zBody zApp`
  ----------------------------------------------------------------------
  have hEv4' : Ev main (mvVal 1 0 4 5) s3 s4 n4 := hEv4
  have hEv5' : Ev main (zMer zApp zF) s4 s5 n5 := hEv5
  have hIB1T : Ev main B1T ⟨gB, X1⟩ s5 (1 + (n3 + (n4 + n5))) :=
    (Ev.seqs_cons hPop2 (Ev.seqs_cons hEv3 (Ev.seqs_cons hEv4' hEv5'))).mono (by omega)
  have hIITE2 : Ev main (seqs [ITE2]) ⟨gB, X1⟩ s5 (2 + (n3 + (n4 + n5))) :=
    (Ev.iteT (by simp only [gB, Function.update_self, hX1_2, hhd2]) hIB1T).mono (by omega)
  have hIB1 : Ev main B1 ⟨gP, X⟩ s5 (4 + (n3 + (n4 + n5))) :=
    (Ev.seqs_cons hPop1 (Ev.seqs_cons hPeek2 hIITE2)).mono (by omega)
  have hIITE1 : Ev main (seqs [ITE1]) ⟨gP, X⟩ s5 (5 + (n3 + (n4 + n5))) :=
    (Ev.iteT (by simp only [gP, Function.update_self, hhd1]) hIB1).mono (by omega)
  have hBody : Ev main (zBody zApp) ⟨g, X⟩ s5 (6 + (n3 + (n4 + n5))) := by
    rw [hzBody]
    exact (Ev.seqs_cons hPeek1 hIITE1).mono (by omega)
  ----------------------------------------------------------------------
  -- The cost bound
  ----------------------------------------------------------------------
  have hcost : 6 + (n3 + (n4 + n5)) ≤ zStepCost KA (r1 :: t1) (r2 :: t2) := by
    rw [zStepCost, zBump_cons, zBump_cons]
    have hAB : KA * (vsz (ofList r1) + 1) +
        100 * (vsz (ofList r1) + 1 + (vsz (ofList r2) + 1)) ≤
        (KA + 100) * (vsz (ofList r1) + 1 + (vsz (ofList r2) + 1)) := by
      rw [add_mul]
      have h1' : KA * (vsz (ofList r1) + 1) ≤
          KA * (vsz (ofList r1) + 1 + (vsz (ofList r2) + 1)) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      omega
    omega
  ----------------------------------------------------------------------
  -- Conclusion
  ----------------------------------------------------------------------
  refine ⟨s5, 6 + (n3 + (n4 + n5)), hBody, hcost, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs5_0, ← h0]
  · rw [hfr5 1 (by decide) (by decide) (by decide) (by decide), hs4_1]
  · rw [hfr5 2 (by decide) (by decide) (by decide) (by decide),
        hfr4 2 (by decide) (by decide) (by decide) (by decide), hs3_2]
  · exact hs5_3
  · exact hs5_reg
  · rw [hs5_4, hs4_4, hs3_4]
    simp only [X2, Function.update_of_ne (by decide : (4 : Stk) ≠ 2),
      X1, Function.update_of_ne (by decide : (4 : Stk) ≠ 1)]
  · rw [hs5_5, hs4_5, hs3_5]
    simp only [X2, Function.update_of_ne (by decide : (5 : Stk) ≠ 2),
      X1, Function.update_of_ne (by decide : (5 : Stk) ≠ 1)]
  · intro k hk0 hk1 hk2 hk3 hk4 hk5
    rw [hfr5 k hk0 hk3 hk4 hk5, hfr4 k hk1 hk0 hk4 hk5, hfr3 k hk2 hk0 hk4 hk5]
    simp only [X2, Function.update_of_ne hk2, X1, Function.update_of_ne hk1]

end Work.SynFFT
