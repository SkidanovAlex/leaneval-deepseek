import Mathlib
import Submission.Work.ConvR.scaleFacts
import Submission.Work.ConvR.flagDefs
import Submission.Work.ConvR.flagAux
import Submission.Work.ConvR.eval_readLoop
import Submission.Work.ConvR.eval_restLoop

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.ConvR

open HvdH

/-- Assembly of `flagWord` from the two loop lemmas (`eval_readLoop`, `eval_restLoop`). -/
theorem flagWord_of
    (hread : ∀ (main : Cmd) (rs rd : Stk) (rf rv : Reg), rd ≠ rs → rv ≠ rf →
      ∀ (l₁ l₂ : List Glyph), Glyph.iend ∉ l₁ → ∀ s : State,
        s.stk rs = l₁ ++ Glyph.iend :: l₂ →
        Eval main (readLoop rs rd rf rv) s
          ((readFin rs rd rv l₁ l₂ s).updReg rf (Glyph.mk 2)) (5 * (l₁.length + 1) + 2))
    (hrest : ∀ (main : Cmd) (rs rd : Stk) (rf rv : Reg) (m : Glyph), rd ≠ rs → rv ≠ rf →
      ∀ (B l₀ : List Glyph), m ∉ B → ∀ s : State, s.stk rs = B ++ m :: l₀ →
        Eval main (restLoop rs rd rf rv m) s
          ((restFin rs rd rv m B l₀ s).updReg rf (Glyph.mk 2)) (4 * (B.length + 1) + 2)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p c M r : ℕ)
      (As : List (List (ℤ × ℤ))) (rest : List HvdH.Val),
      HvdH.InDiscArr p M r As →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: HvdH.rarrVal As :: rest)
        (fun _ out => ∃ fg : HvdH.Val,
          out = fg :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: HvdH.rarrVal As :: rest ∧
          ((∀ u ∈ As, u = []) → fg = HvdH.Val.int 0) ∧
          ((∃ u ∈ As, u ≠ []) → fg = HvdH.Val.int 1))
        (fun vs => K * (HvdH.vsz (vs.getD 0 HvdH.Val.nil) + HvdH.vsz (vs.getD 1 HvdH.Val.nil) + 1)) := by
  refine ⟨flagProg, 16, ?_⟩
  intro main p c M r As rest hDisc vs hvs s R hR
  rw [hvs] at hR
  set Wp : List Glyph := (Val.int (p : ℤ)).enc with hWp
  set Wc : List Glyph := (Val.int (c : ℤ)).enc with hWc
  set Wa : List Glyph := (rarrVal As).enc with hWa
  set Lr : List Glyph := encs rest ++ R with hLr
  have h0 : s.stk 0 = Wp ++ (Wc ++ (Wa ++ Lr)) := by
    rw [hR, encs_three, ← hWp, ← hWc, ← hWa, ← hLr]
  -- phase 1: the frame marker
  have hA : Eval main (Cmd.seq (Cmd.set 3 (Glyph.mk 3)) (Cmd.push 1 3)) s (stA s) 2 :=
    eval_marker main s
  -- phase 2: read the encoding of `p`
  have hsA0 : (stA s).stk 0 = intBody (p : ℤ) ++ Glyph.iend :: (Wc ++ (Wa ++ Lr)) := by
    rw [stA_stk0, h0, hWp, intEnc_eq (p : ℤ), List.append_assoc, List.singleton_append]
  set sB : State := stB (stA s) (intBody (p : ℤ)) (Wc ++ (Wa ++ Lr)) with hsB
  have hB : Eval main (readLoop 0 1 0 1) (stA s) sB (5 * ((intBody (p : ℤ)).length + 1) + 2) := by
    rw [hsB]
    exact hread main 0 1 0 1 (by decide : (1 : Stk) ≠ 0) (by decide : (1 : Reg) ≠ 0)
      _ _ (iend_notMem_intBody _) (stA s) hsA0
  have hsB0 : sB.stk 0 = Wc ++ (Wa ++ Lr) := by rw [hsB, stB_stk0]
  have hsB1 : sB.stk 1 = Wp.reverse ++ (Glyph.mk 3 :: s.stk 1) := by
    rw [hsB, stB_stk1, stA_stk1, ← intEnc_eq (p : ℤ), ← hWp]
  -- phase 3: read the encoding of `c`
  have hsB0' : sB.stk 0 = intBody (c : ℤ) ++ Glyph.iend :: (Wa ++ Lr) := by
    rw [hsB0, hWc, intEnc_eq (c : ℤ), List.append_assoc, List.singleton_append]
  set sC : State := stB sB (intBody (c : ℤ)) (Wa ++ Lr) with hsC
  have hC : Eval main (readLoop 0 1 0 1) sB sC (5 * ((intBody (c : ℤ)).length + 1) + 2) := by
    rw [hsC]
    exact hread main 0 1 0 1 (by decide : (1 : Stk) ≠ 0) (by decide : (1 : Reg) ≠ 0)
      _ _ (iend_notMem_intBody _) sB hsB0'
  have hsC0 : sC.stk 0 = Wa ++ Lr := by rw [hsC, stB_stk0]
  have hsC1 : sC.stk 1 = Wc.reverse ++ (Wp.reverse ++ (Glyph.mk 3 :: s.stk 1)) := by
    rw [hsC, stB_stk1, hsB1, ← intEnc_eq (c : ℤ), ← hWc]
  -- generic cost facts
  have hlp : (intBody (p : ℤ)).length + 1 = isz (p : ℤ) := intBody_length _
  have hlc : (intBody (c : ℤ)).length + 1 = isz (c : ℤ) := intBody_length _
  have hS : 4 ≤ isz (p : ℤ) + isz (c : ℤ) := by
    have h1 := isz_lower (p : ℤ); have h2 := isz_lower (c : ℤ); omega
  have hvsz0 : vsz (vs.getD 0 Val.nil) = isz (p : ℤ) := by simp [hvs, vsz_int]
  have hvsz1 : vsz (vs.getD 1 Val.nil) = isz (c : ℤ) := by simp [hvs, vsz_int]
  cases As with
  | nil =>
    have hWaN : Wa = [Glyph.nil] := by rw [hWa]; rfl
    have hsC0n : sC.stk 0 = Glyph.nil :: Lr := by rw [hsC0, hWaN]; rfl
    set B0 : List Glyph := Wc.reverse ++ Wp.reverse with hB0
    set sD : State := flagNilOut sC with hsD
    set sE : State := stE sD B0 (s.stk 1) with hsE
    set sF : State := stF 0 sE with hsF
    have hD : Eval main flagDecide sC sD 3 := by rw [hsD]; exact eval_flagDecide_nil main hsC0n
    have hD1 : sD.stk 1 = B0 ++ Glyph.mk 3 :: s.stk 1 := by
      rw [hsD, flagNilOut_stk, hsC1, hB0]
      simp [List.append_assoc]
    have hmB : Glyph.mk 3 ∉ B0 := by
      rw [hB0, List.mem_append]
      rintro (h | h)
      · rw [hWc] at h; exact mk3_notMem_intEnc_reverse (c : ℤ) h
      · rw [hWp] at h; exact mk3_notMem_intEnc_reverse (p : ℤ) h
    have hE : Eval main (restLoop 1 0 0 1 (Glyph.mk 3)) sD sE (4 * (B0.length + 1) + 2) := by
      rw [hsE]; exact eval_rest hrest main sD B0 (s.stk 1) hmB hD1
    have hE0 : sE.stk 0 = B0.reverse ++ sD.stk 0 := by rw [hsE, stE_stk0]
    have hE1 : sE.stk 1 = s.stk 1 := by rw [hsE, stE_stk1]
    have hEreg : sE.reg 2 = Glyph.pos := by rw [hsE, stE_reg2, hsD, flagNilOut_reg2]
    have hEne : ∀ k : Stk, k ≠ 0 → k ≠ 1 → sE.stk k = sC.stk k := by
      intro k hk0 hk1
      rw [hsE, stE_stk_ne _ _ _ hk0 hk1, hsD, flagNilOut_stk]
    have hF : Eval main (Cmd.ite 2 Glyph.pos (pushIntVal 0 4) (pushIntVal 1 4)) sE sF
        (1 + Work.Kernel.pushGlyphsCost ((Val.int ((0 : ℕ) : ℤ)).enc.reverse)) := by
      rw [hsF]; exact eval_pushFlag0 main sE hEreg
    have hF0 : sF.stk 0 = (Val.int ((0 : ℕ) : ℤ)).enc ++ sE.stk 0 := by rw [hsF, stF_stk0]
    set N : ℕ :=
      2 + (5 * ((intBody (p : ℤ)).length + 1) + 2 + (5 * ((intBody (c : ℤ)).length + 1) + 2
        + (3 + (4 * (B0.length + 1) + 2
          + (1 + Work.Kernel.pushGlyphsCost ((Val.int ((0 : ℕ) : ℤ)).enc.reverse))))))
      with hN
    have hev : Eval main flagProg s sF N := by
      rw [hN]
      exact Eval.seq hA (Eval.seq hB (Eval.seq hC (Eval.seq hD (Eval.seq hE hF))))
    have hbound : N ≤ 16 * (vsz (vs.getD 0 Val.nil) + vsz (vs.getD 1 Val.nil) + 1) := by
      rw [hN, hvsz0, hvsz1]
      have hb : Work.Kernel.pushGlyphsCost ((Val.int ((0 : ℕ) : ℤ)).enc.reverse) ≤ 9 := by
        rw [pushGlyphsCost_intEnc 0]
        have := isz_natCast_zero_le
        omega
      have hBl : B0.length = isz (c : ℤ) + isz (p : ℤ) := by
        rw [hB0, List.length_append, List.length_reverse, List.length_reverse, hWc, hWp,
          intEnc_length, intEnc_length]
      omega
    refine ⟨Val.int 0 :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal ([] : List (List (ℤ × ℤ))) :: rest,
      sF, N, ?_, hev, hbound, ?_, ?_⟩
    · refine ⟨Val.int 0, rfl, ?_, ?_⟩
      · intro _; rfl
      · rintro ⟨u, hu, _⟩
        simp at hu
    · have hLHS : sF.stk 0 = (Val.int ((0 : ℕ) : ℤ)).enc ++ (Wp ++ (Wc ++ (Wa ++ Lr))) := by
        rw [hF0, hE0, hsD, flagNilOut_stk, hsC0, hB0, reverse_append_reverse]
        simp [List.append_assoc]
      rw [hLHS, encs_three, Work.Kernel.encs_cons, List.append_assoc, ← hWa, ← hLr, ← hWp, ← hWc]
      norm_num
    · intro k hk0
      by_cases hk1 : k = 1
      · subst hk1
        rw [hsF, stF_stk_ne _ _ (by decide : (1 : Stk) ≠ 0), hE1]
      · rw [hsF, stF_stk_ne _ _ hk0, hEne k hk0 hk1, hsC, stB_stk_ne _ _ _ hk0 hk1, hsB,
          stB_stk_ne _ _ _ hk0 hk1, stA_stk_ne _ hk0 hk1]
  | cons w ws =>
    have hWaC : Wa = Glyph.cons :: ((cvecVal w).enc ++ (rarrVal ws).enc) := by rw [hWa]; simp
    cases w with
    | nil =>
      set X : List Glyph := (rarrVal ws).enc ++ Lr with hX
      have hWaR : Wa = Glyph.cons :: (Glyph.nil :: (rarrVal ws).enc) := by rw [hWaC]; simp
      have hsC0c : sC.stk 0 = Glyph.cons :: Glyph.nil :: X := by
        rw [hsC0, hWaR]
        simp [List.append_assoc, hX]
      set B0 : List Glyph := Glyph.cons :: (Wc.reverse ++ Wp.reverse) with hB0
      set sD : State := flagRowNilOut sC X with hsD
      set sE : State := stE sD B0 (s.stk 1) with hsE
      set sF : State := stF 0 sE with hsF
      have hD : Eval main flagDecide sC sD 8 := by
        rw [hsD]; exact eval_flagDecide_rowNil main X sC hsC0c
      have hD1 : sD.stk 1 = B0 ++ Glyph.mk 3 :: s.stk 1 := by
        rw [hsD, flagRowNilOut_stk1, hsC1, hB0]
        simp [List.append_assoc]
      have hmB : Glyph.mk 3 ∉ B0 := by
        rw [hB0, List.mem_cons]
        rintro (h | h)
        · exact absurd h (by decide)
        · rw [List.mem_append] at h
          rcases h with h | h
          · rw [hWc] at h; exact mk3_notMem_intEnc_reverse (c : ℤ) h
          · rw [hWp] at h; exact mk3_notMem_intEnc_reverse (p : ℤ) h
      have hE : Eval main (restLoop 1 0 0 1 (Glyph.mk 3)) sD sE (4 * (B0.length + 1) + 2) := by
        rw [hsE]; exact eval_rest hrest main sD B0 (s.stk 1) hmB hD1
      have hE0 : sE.stk 0 = B0.reverse ++ sD.stk 0 := by rw [hsE, stE_stk0]
      have hE1 : sE.stk 1 = s.stk 1 := by rw [hsE, stE_stk1]
      have hEreg : sE.reg 2 = Glyph.pos := by rw [hsE, stE_reg2, hsD, flagRowNilOut_reg2]
      have hEne : ∀ k : Stk, k ≠ 0 → k ≠ 1 → sE.stk k = sC.stk k := by
        intro k hk0 hk1
        rw [hsE, stE_stk_ne _ _ _ hk0 hk1, hsD, flagRowNilOut_stk_ne _ _ hk0 hk1]
      have hF : Eval main (Cmd.ite 2 Glyph.pos (pushIntVal 0 4) (pushIntVal 1 4)) sE sF
          (1 + Work.Kernel.pushGlyphsCost ((Val.int ((0 : ℕ) : ℤ)).enc.reverse)) := by
        rw [hsF]; exact eval_pushFlag0 main sE hEreg
      have hF0 : sF.stk 0 = (Val.int ((0 : ℕ) : ℤ)).enc ++ sE.stk 0 := by rw [hsF, stF_stk0]
      set N : ℕ :=
        2 + (5 * ((intBody (p : ℤ)).length + 1) + 2 + (5 * ((intBody (c : ℤ)).length + 1) + 2
          + (8 + (4 * (B0.length + 1) + 2
            + (1 + Work.Kernel.pushGlyphsCost ((Val.int ((0 : ℕ) : ℤ)).enc.reverse))))))
        with hN
      have hev : Eval main flagProg s sF N := by
        rw [hN]
        exact Eval.seq hA (Eval.seq hB (Eval.seq hC (Eval.seq hD (Eval.seq hE hF))))
      have hbound : N ≤ 16 * (vsz (vs.getD 0 Val.nil) + vsz (vs.getD 1 Val.nil) + 1) := by
        rw [hN, hvsz0, hvsz1]
        have hb : Work.Kernel.pushGlyphsCost ((Val.int ((0 : ℕ) : ℤ)).enc.reverse) ≤ 9 := by
          rw [pushGlyphsCost_intEnc 0]
          have := isz_natCast_zero_le
          omega
        have hBl : B0.length = isz (c : ℤ) + isz (p : ℤ) + 1 := by
          rw [hB0, List.length_cons, List.length_append, List.length_reverse, List.length_reverse,
            hWc, hWp, intEnc_length, intEnc_length]
        omega
      have hall : ∀ u ∈ ([] : List (ℤ × ℤ)) :: ws, u = [] := all_nil_of_head_nil hDisc rfl
      refine ⟨Val.int 0 :: Val.int (p : ℤ) :: Val.int (c : ℤ)
        :: rarrVal (([] : List (ℤ × ℤ)) :: ws) :: rest,
        sF, N, ?_, hev, hbound, ?_, ?_⟩
      · refine ⟨Val.int 0, rfl, ?_, ?_⟩
        · intro _; rfl
        · rintro ⟨u, hu, hne⟩
          exact absurd (hall u hu) hne
      · have hLHS : sF.stk 0 = (Val.int ((0 : ℕ) : ℤ)).enc ++ (Wp ++ (Wc ++ (Wa ++ Lr))) := by
          rw [hF0, hE0, hsD, flagRowNilOut_stk0, hB0, List.reverse_cons, reverse_append_reverse]
          simp [List.append_assoc, hWaR, hX]
        rw [hLHS, encs_three, Work.Kernel.encs_cons, List.append_assoc, ← hWa, ← hLr, ← hWp, ← hWc]
        norm_num
      · intro k hk0
        by_cases hk1 : k = 1
        · subst hk1
          rw [hsF, stF_stk_ne _ _ (by decide : (1 : Stk) ≠ 0), hE1]
        · rw [hsF, stF_stk_ne _ _ hk0, hEne k hk0 hk1, hsC, stB_stk_ne _ _ _ hk0 hk1, hsB,
            stB_stk_ne _ _ _ hk0 hk1, stA_stk_ne _ hk0 hk1]
    | cons z u =>
      set X : List Glyph := ((cfxVal z).enc ++ (cvecVal u).enc) ++ ((rarrVal ws).enc ++ Lr) with hX
      have hWaR : Wa = Glyph.cons :: (Glyph.cons :: (((cfxVal z).enc ++ (cvecVal u).enc) ++ (rarrVal ws).enc)) := by
        rw [hWaC]; simp [List.append_assoc]
      have hsC0c : sC.stk 0 = Glyph.cons :: Glyph.cons :: X := by
        rw [hsC0, hWaR]
        simp [List.append_assoc, hX]
      set B0 : List Glyph := Glyph.cons :: (Wc.reverse ++ Wp.reverse) with hB0
      set sD : State := flagRowConsOut sC Glyph.cons X with hsD
      set sE : State := stE sD B0 (s.stk 1) with hsE
      set sF : State := stF 1 sE with hsF
      have hD : Eval main flagDecide sC sD 8 := by
        rw [hsD]; exact eval_flagDecide_rowCons main X sC Glyph.cons (by decide) hsC0c
      have hD1 : sD.stk 1 = B0 ++ Glyph.mk 3 :: s.stk 1 := by
        rw [hsD, flagRowConsOut_stk1, hsC1, hB0]
        simp [List.append_assoc]
      have hmB : Glyph.mk 3 ∉ B0 := by
        rw [hB0, List.mem_cons]
        rintro (h | h)
        · exact absurd h (by decide)
        · rw [List.mem_append] at h
          rcases h with h | h
          · rw [hWc] at h; exact mk3_notMem_intEnc_reverse (c : ℤ) h
          · rw [hWp] at h; exact mk3_notMem_intEnc_reverse (p : ℤ) h
      have hE : Eval main (restLoop 1 0 0 1 (Glyph.mk 3)) sD sE (4 * (B0.length + 1) + 2) := by
        rw [hsE]; exact eval_rest hrest main sD B0 (s.stk 1) hmB hD1
      have hE0 : sE.stk 0 = B0.reverse ++ sD.stk 0 := by rw [hsE, stE_stk0]
      have hE1 : sE.stk 1 = s.stk 1 := by rw [hsE, stE_stk1]
      have hEreg : sE.reg 2 = Glyph.neg := by rw [hsE, stE_reg2, hsD, flagRowConsOut_reg2]
      have hEne : ∀ k : Stk, k ≠ 0 → k ≠ 1 → sE.stk k = sC.stk k := by
        intro k hk0 hk1
        rw [hsE, stE_stk_ne _ _ _ hk0 hk1, hsD, flagRowConsOut_stk_ne _ _ _ hk0 hk1]
      have hF : Eval main (Cmd.ite 2 Glyph.pos (pushIntVal 0 4) (pushIntVal 1 4)) sE sF
          (1 + Work.Kernel.pushGlyphsCost ((Val.int ((1 : ℕ) : ℤ)).enc.reverse)) := by
        rw [hsF]; exact eval_pushFlag1 main sE hEreg
      have hF0 : sF.stk 0 = (Val.int ((1 : ℕ) : ℤ)).enc ++ sE.stk 0 := by rw [hsF, stF_stk0]
      set N : ℕ :=
        2 + (5 * ((intBody (p : ℤ)).length + 1) + 2 + (5 * ((intBody (c : ℤ)).length + 1) + 2
          + (8 + (4 * (B0.length + 1) + 2
            + (1 + Work.Kernel.pushGlyphsCost ((Val.int ((1 : ℕ) : ℤ)).enc.reverse))))))
        with hN
      have hev : Eval main flagProg s sF N := by
        rw [hN]
        exact Eval.seq hA (Eval.seq hB (Eval.seq hC (Eval.seq hD (Eval.seq hE hF))))
      have hbound : N ≤ 16 * (vsz (vs.getD 0 Val.nil) + vsz (vs.getD 1 Val.nil) + 1) := by
        rw [hN, hvsz0, hvsz1]
        have hb : Work.Kernel.pushGlyphsCost ((Val.int ((1 : ℕ) : ℤ)).enc.reverse) ≤ 9 := by
          rw [pushGlyphsCost_intEnc 1]
          have := isz_natCast_one_le
          omega
        have hBl : B0.length = isz (c : ℤ) + isz (p : ℤ) + 1 := by
          rw [hB0, List.length_cons, List.length_append, List.length_reverse, List.length_reverse,
            hWc, hWp, intEnc_length, intEnc_length]
        omega
      refine ⟨Val.int 1 :: Val.int (p : ℤ) :: Val.int (c : ℤ)
        :: rarrVal ((z :: u) :: ws) :: rest,
        sF, N, ?_, hev, hbound, ?_, ?_⟩
      · refine ⟨Val.int 1, rfl, ?_, ?_⟩
        · rintro hnil
          exact absurd (hnil (z :: u) (List.mem_cons_self ..)) (by simp)
        · intro _; rfl
      · have hLHS : sF.stk 0 = (Val.int ((1 : ℕ) : ℤ)).enc ++ (Wp ++ (Wc ++ (Wa ++ Lr))) := by
          rw [hF0, hE0, hsD, flagRowConsOut_stk0, hB0, List.reverse_cons, reverse_append_reverse]
          simp [List.append_assoc, hWaR, hX]
        rw [hLHS, encs_three, Work.Kernel.encs_cons, List.append_assoc, ← hWa, ← hLr, ← hWp, ← hWc]
        norm_num
      · intro k hk0
        by_cases hk1 : k = 1
        · subst hk1
          rw [hsF, stF_stk_ne _ _ (by decide : (1 : Stk) ≠ 0), hE1]
        · rw [hsF, stF_stk_ne _ _ hk0, hEne k hk0 hk1, hsC, stB_stk_ne _ _ _ hk0 hk1, hsB,
            stB_stk_ne _ _ _ hk0 hk1, stA_stk_ne _ hk0 hk1]


/-- The requested flag word. -/
theorem flagWord :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p c M r : ℕ)
      (As : List (List (ℤ × ℤ))) (rest : List HvdH.Val),
      HvdH.InDiscArr p M r As →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: HvdH.rarrVal As :: rest)
        (fun _ out => ∃ fg : HvdH.Val,
          out = fg :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: HvdH.rarrVal As :: rest ∧
          ((∀ u ∈ As, u = []) → fg = HvdH.Val.int 0) ∧
          ((∃ u ∈ As, u ≠ []) → fg = HvdH.Val.int 1))
        (fun vs => K * (HvdH.vsz (vs.getD 0 HvdH.Val.nil) + HvdH.vsz (vs.getD 1 HvdH.Val.nil) + 1)) :=
  flagWord_of
    (fun main rs rd rf rv hrd hrv l₁ l₂ hno s hstk =>
      eval_readLoop main rs rd rf rv hrd hrv l₁ l₂ hno s hstk)
    (fun main rs rd rf rv m hrd hrv B l₀ hm s hstk =>
      eval_restLoop main rs rd rf rv m hrd hrv B l₀ hm s hstk)

end Work.ConvR
