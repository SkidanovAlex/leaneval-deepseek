import Mathlib
import Submission.Work.SynFFT.zipKit

namespace Work.SynFFT

open HvdH
open Work.Layout

set_option maxHeartbeats 1000000

/-- One iteration of the `zipCat` loop when the first group is nonempty and the second exhausted:
the body takes the head row `r1` of stack `1`, pushes the empty row (`nil`, i.e. `ofList []`) on the
value stack and merges it as the *second* operand, so the merged row is `ofList (r1 ++ [])` and the
exhausted group contributes like `zipCat (r1 :: t1) []`.  See `Work.SynFFT.zipStepCC` for the
available sub-lemmas (`Work.SynFFT.zMer_ev`, `Work.Layout.mvVal_ev_full`,
`Work.Layout.pushConst_ev`, `Work.Layout.ev_peek'`, `Work.Layout.ev_pop'`,
`Work.Layout.Ev.seq'`, `Work.Layout.Ev.iteT`, `Work.Layout.Ev.iteF`); the cost is
`Work.SynFFT.zStepCost KA (r1 :: t1) [] = (KA + 100) * (vsz (ofList r1) + 1)`
(`zBump_cons`, `zBump_nil`). -/
theorem zipStepCN {main zApp : HvdH.Cmd} {KA : ℕ}
    (hApp : ∀ (xs ys rest' : List HvdH.Val), HvdH.WordR main zApp
      (fun vs => vs = HvdH.ofList xs :: HvdH.ofList ys :: rest')
      (fun _ out => out = HvdH.ofList (xs ++ ys) :: rest')
      (fun _ => KA * (HvdH.vsz (HvdH.ofList xs) + 1)))
    {rest : List HvdH.Val} {R : List HvdH.Glyph} {r1 : List HvdH.Val}
    {t1 : List (List HvdH.Val)} {Racc : List (List HvdH.Val)} {Z1 Z2 Z3 : List HvdH.Glyph}
    {g : HvdH.Reg → HvdH.Glyph} {X : HvdH.Stk → List HvdH.Glyph}
    (h0 : X 0 = HvdH.encs rest ++ R)
    (h1 : X 1 = HvdH.Glyph.cons :: ((HvdH.ofList r1).enc ++
      ((HvdH.ofList (t1.map HvdH.ofList)).enc ++ Z1)))
    (h2 : X 2 = (HvdH.ofList ([] : List HvdH.Val)).enc ++ Z2)
    (h3 : X 3 = (HvdH.ofList (Racc.map HvdH.ofList)).enc ++ Z3) :
    ∃ s' n, Work.Layout.Ev main (Work.SynFFT.zBody zApp) ⟨g, X⟩ s' n ∧
      n ≤ Work.SynFFT.zStepCost KA (r1 :: t1) [] ∧
      s'.stk 0 = X 0 ∧
      s'.stk 1 = (HvdH.ofList (t1.map HvdH.ofList)).enc ++ Z1 ∧
      s'.stk 2 = X 2 ∧
      s'.stk 3 = (HvdH.ofList ((HvdH.ofList (r1 ++ ([] : List HvdH.Val))) ::
        Racc.map HvdH.ofList)).enc ++ Z3 ∧
      s'.reg Work.SynFFT.zF = HvdH.Glyph.cons ∧
      s'.stk 4 = X 4 ∧ s'.stk 5 = X 5 ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 5 → s'.stk k = X k) := by
  -- The heads of stacks `1` and `2` are `cons` and `nil` respectively.
  have hX1 : (X 1).headD Glyph.eos = Glyph.cons := by rw [h1]; rfl
  have hX2 : (X 2).headD Glyph.eos = Glyph.nil := by rw [h2]; rfl
  -- The intermediate states of the loop body, one `let` per primitive of the taken path:
  -- after `peek 1 zP`, after `pop 1 rA`, after `peek 2 zP`.
  let σ1 : State := ⟨Function.update g zP Glyph.cons, X⟩
  let σ2 : State := ⟨Function.update σ1.reg rA Glyph.cons, Function.update X 1 (X 1).tail⟩
  let σ3 : State := ⟨Function.update σ2.reg zP Glyph.nil, σ2.stk⟩
  -- The sub-programs of `zBody zApp`.
  let B1T : Cmd := seqs [.pop 2 rA, mvVal 2 0 4 5, mvVal 1 0 4 5, zMer zApp zF]
  let B1F : Cmd := seqs [Work.Layout.pushConst 0 Glyph.nil, mvVal 1 0 4 5, zMer zApp zF]
  let B1 : Cmd := seqs [.pop 1 rA, .peek 2 zP, .ite zP Glyph.cons B1T B1F]
  let B2 : Cmd := seqs [.peek 2 zP, .ite zP Glyph.cons
      (seqs [Work.Layout.pushConst 0 Glyph.nil, .pop 2 rA, mvVal 2 0 4 5, zMer zApp zF])
      (.set zF Glyph.eos)]
  -- Stack contents of the intermediate states.
  have hσ2 : ∀ k : Stk, k ≠ 1 → σ2.stk k = X k := by
    intro k hk
    simp only [σ2]
    exact stkFn_ne X hk (X 1).tail
  have hσ2_1 : σ2.stk 1 = (ofList r1).enc ++ ((ofList (t1.map ofList)).enc ++ Z1) := by
    simp only [σ2, stkFn_same]
    rw [h1, List.tail_cons]
  have hσ2_head : (σ2.stk 2).headD Glyph.eos = Glyph.nil := by
    rw [hσ2 2 (by decide)]; exact hX2
  have hσ3 : ∀ k : Stk, σ3.stk k = σ2.stk k := by intro k; rfl
  have hσ3_reg : σ3.reg zP = Glyph.nil := by simp only [σ3, Function.update_self]
  have hσ3_reg_ne : σ3.reg zP ≠ Glyph.cons := by rw [hσ3_reg]; decide
  have hσ1_reg : σ1.reg zP = Glyph.cons := by simp only [σ1, Function.update_self]
  -- `peek 1 zP` (reads `cons`), `pop 1 rA`, `peek 2 zP` (reads `nil`).
  have hpeek1 : Ev main (.peek 1 zP) ⟨g, X⟩ σ1 1 := by
    simpa only [σ1, hX1] using ev_peek' main 1 zP g X
  have hpop : Ev main (.pop 1 rA) σ1 σ2 1 := by
    simpa only [σ1, σ2, hX1] using ev_pop' main 1 rA σ1.reg σ1.stk
  have hpeek2 : Ev main (.peek 2 zP) σ2 σ3 1 := by
    simpa only [σ3, hσ2_head] using ev_peek' main 2 zP σ2.reg σ2.stk
  -- `pushConst 0 Glyph.nil`: push the empty row on the value stack.
  obtain ⟨σ4, n4, hpush, hn4, hσ4_0', hσ4_ne, -, -⟩ :=
    Work.Layout.pushConst_ev (main := main) (k := (0 : Stk)) (cst := Glyph.nil)
      (g := σ3.reg) (X := σ3.stk)
  have hσ4_0 : σ4.stk 0 = encs (ofList ([] : List Val) :: rest) ++ R := by
    rw [hσ4_0', hσ3 0, hσ2 0 (by decide), h0]; rfl
  have hσ4_1 : σ4.stk 1 = (ofList r1).enc ++ ((ofList (t1.map ofList)).enc ++ Z1) := by
    rw [hσ4_ne 1 (by decide), hσ3 1, hσ2_1]
  have hσ4_3 : σ4.stk 3 = (ofList (Racc.map ofList)).enc ++ Z3 := by
    rw [hσ4_ne 3 (by decide), hσ3 3, hσ2 3 (by decide), h3]
  have hσ4_4 : σ4.stk 4 = X 4 := by rw [hσ4_ne 4 (by decide), hσ3 4, hσ2 4 (by decide)]
  have hσ4_5 : σ4.stk 5 = X 5 := by rw [hσ4_ne 5 (by decide), hσ3 5, hσ2 5 (by decide)]
  have hσ4_2 : σ4.stk 2 = X 2 := by rw [hσ4_ne 2 (by decide), hσ3 2, hσ2 2 (by decide)]
  -- `mvVal 1 0 4 5`: move the head row `ofList r1` of stack `1` on top of the value stack.
  obtain ⟨σ5, n5, hmv, hn5, hσ5_1, hσ5_0, hσ5_4, hσ5_5, hσ5_oth⟩ :=
    mvVal_ev_full (main := main) (a := (1 : Stk)) (b := (0 : Stk)) (c := (4 : Stk)) (d := (5 : Stk))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := σ4.reg) (X := σ4.stk) (v := ofList r1) (A := (ofList (t1.map ofList)).enc ++ Z1)
      (B := encs (ofList ([] : List Val) :: rest) ++ R) hσ4_1 hσ4_0
  have hσ5_0' : σ5.stk 0 = encs (ofList r1 :: ofList ([] : List Val) :: rest) ++ R := by
    simp only [hσ5_0, encs, List.map_cons, List.flatten_cons, List.append_assoc]
  have hσ5_3 : σ5.stk 3 = (ofList (Racc.map ofList)).enc ++ Z3 := by
    rw [hσ5_oth 3 (by decide) (by decide) (by decide) (by decide), hσ4_3]
  -- `zMer zApp zF`: merge `ofList r1` with the empty row and prepend the result to the accumulator.
  obtain ⟨s', n6, hmer, hn6, hs'0, hs'3, hs'F, hs'4, hs'5, hs'oth⟩ :=
    zMer_ev (main := main) (zApp := zApp) (KA := KA) (f := zF) hApp
      (rest := rest) (R := R) (r₁ := r1) (r₂ := []) (Racc := Racc) (Z3 := Z3)
      (g := σ5.reg) (X := σ5.stk) hσ5_0' hσ5_3
  -- Composing the six primitives of the taken path.
  have hB1F : Ev main B1F σ3 s' (n4 + (n5 + n6)) :=
    Ev.seqs_cons (cs := [mvVal 1 0 4 5, zMer zApp zF]) hpush
      (Ev.seqs_cons (cs := [zMer zApp zF]) hmv hmer)
  have hite2 : Ev main (.ite zP Glyph.cons B1T B1F) σ3 s' (n4 + (n5 + n6) + 1) :=
    Ev.iteF hσ3_reg_ne hB1F
  have hB1 : Ev main B1 σ1 s' (1 + (1 + (n4 + (n5 + n6) + 1))) :=
    Ev.seqs_cons (cs := [.peek 2 zP, .ite zP Glyph.cons B1T B1F]) hpop
      (Ev.seqs_cons (cs := [.ite zP Glyph.cons B1T B1F]) hpeek2 hite2)
  have hite1 : Ev main (.ite zP Glyph.cons B1 B2) σ1 s' (1 + (1 + (n4 + (n5 + n6) + 1)) + 1) :=
    Ev.iteT hσ1_reg hB1
  have hbody : Ev main (zBody zApp) ⟨g, X⟩ s' (n4 + (n5 + n6) + 5) := by
    have h := Ev.seqs_cons (cs := [.ite zP Glyph.cons B1 B2]) hpeek1 hite1
    have h' : Ev main (zBody zApp) ⟨g, X⟩ s' (1 + (1 + (1 + (n4 + (n5 + n6) + 1)) + 1)) := by
      simpa only [zBody, B1, B2, B1T, B1F] using h
    exact h'.mono (by omega)
  refine ⟨s', n4 + (n5 + n6) + 5, hbody, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost: `(KA + 36) * (vsz (ofList r1) + 1) + 13 ≤ (KA + 100) * (vsz (ofList r1) + 1)`
    have hv : 1 ≤ vsz (ofList r1) := one_le_vsz _
    have hv0 : vsz (ofList ([] : List Val)) = 1 := rfl
    have hn6' : n6 ≤ KA * (vsz (ofList r1) + 1) + 20 * (vsz (ofList r1) + 1) + 6 := by
      have h := hn6; rw [hv0] at h; exact h
    have hz : zStepCost KA (r1 :: t1) [] = (KA + 100) * (vsz (ofList r1) + 1) := by
      simp [zStepCost, zBump_cons, zBump_nil]
    rw [hz, Nat.add_mul]
    omega
  · rw [hs'0, h0]
  · rw [hs'oth 1 (by decide) (by decide) (by decide) (by decide), hσ5_1]
  · rw [hs'oth 2 (by decide) (by decide) (by decide) (by decide),
      hσ5_oth 2 (by decide) (by decide) (by decide) (by decide), hσ4_2]
  · exact hs'3
  · exact hs'F
  · rw [hs'4, hσ5_4, hσ4_4]
  · rw [hs'5, hσ5_5, hσ4_5]
  · intro k hk0 hk1 hk2 hk3 hk4 hk5
    rw [hs'oth k hk0 hk3 hk4 hk5, hσ5_oth k hk1 hk0 hk4 hk5, hσ4_ne k hk0, hσ3 k, hσ2 k hk1]

end Work.SynFFT
