import Mathlib
import Submission.Work.Resample.auSetupRunAux
import Submission.Work.Resample.auSplit

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH
open Work.Layout

/-! ## Two small program helpers -/

/-- The register used by `pushNil`. -/
def auSetupR : Reg := ⟨15, by decide⟩

/-- Push the encoding of `Val.nil` onto stack `k`. -/
def pushNil (k : Stk) : Cmd := Cmd.seq (Cmd.set auSetupR Glyph.nil) (Cmd.push k auSetupR)

theorem pushNil_ev (main : Cmd) (k : Stk) (s : State) :
    ∃ s' n, Ev main (pushNil k) s s' n ∧ n ≤ 2 ∧ s'.stk k = Glyph.nil :: s.stk k ∧
      (∀ j, j ≠ k → s'.stk j = s.stk j) := by
  refine ⟨⟨Function.update s.reg auSetupR Glyph.nil,
    Function.update s.stk k (Glyph.nil :: s.stk k)⟩, 2, ?_, le_rfl, ?_, ?_⟩
  · refine ⟨2, ?_, le_rfl⟩
    have h1 : Eval main (Cmd.set auSetupR Glyph.nil) s
        ⟨Function.update s.reg auSetupR Glyph.nil, s.stk⟩ 1 := Eval.set auSetupR Glyph.nil s
    have h2 : Eval main (Cmd.push k auSetupR)
        ⟨Function.update s.reg auSetupR Glyph.nil, s.stk⟩
        ⟨Function.update s.reg auSetupR Glyph.nil,
          Function.update s.stk k ((Function.update s.reg auSetupR Glyph.nil) auSetupR :: s.stk k)⟩ 1 :=
      Eval.push k auSetupR ⟨Function.update s.reg auSetupR Glyph.nil, s.stk⟩
    have h2' : Eval main (Cmd.push k auSetupR)
        ⟨Function.update s.reg auSetupR Glyph.nil, s.stk⟩
        ⟨Function.update s.reg auSetupR Glyph.nil,
          Function.update s.stk k (Glyph.nil :: s.stk k)⟩ 1 := by
      simpa using h2
    exact Eval.seq h1 h2'
  · exact Function.update_self ..
  · intro j hj
    exact Function.update_of_ne hj _ _

/-- A `Pipe` applied to an explicit state. -/
theorem pipe_state {main prog : Cmd} {A B : List Val} {c : ℕ} (h : Pipe main prog A B c)
    (s : State) {R : List Glyph} {Tail : List Val} (h0 : s.stk 0 = encs (A ++ Tail) ++ R) :
    ∃ s' n, Ev main prog s s' n ∧ n ≤ c ∧ s'.stk 0 = encs (B ++ Tail) ++ R ∧
      (∀ k, k ≠ 0 → s'.stk k = s.stk k) := by
  obtain ⟨out, s', n, hout, hev, hn, h0', hk⟩ := h Tail (A ++ Tail) rfl s R h0
  exact ⟨s', n, ⟨n, hev, le_rfl⟩, hn, by rw [h0', hout], hk⟩

/-! ## The main statement -/

theorem auSetupRun (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (u : List (ℤ × ℤ))
      (rest : List HvdH.Val),
      u.length = s → (∀ z ∈ u, HvdH.inDisc p z) → 2 ≤ s → 2 ≤ α → 100 ≤ p → α ^ 2 < p → s < t →
      Work.Resample.WordM main prog
        (fun vs a => vs = HvdH.ofList (u.map HvdH.cfxVal) :: Work.Resample.auPvals p α s t ++ rest ∧
          (∀ k, k ≠ 0 → a k = []))
        (fun vs a out b => out = HvdH.ofList (Work.Resample.auWinV p α s t u 0) ::
            Work.Resample.auPvals p α s t ++ rest ∧
          b 1 = Work.Resample.auRecsF p α s t ++ [HvdH.Val.nil] ∧
          b 2 = Work.Resample.auElems p α s u ++ [HvdH.Val.nil] ∧
          b 3 = [HvdH.Val.nil] ∧ (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → b k = a k))
        (fun vs a => K * ((s + t * Work.Resample.auL p α + Work.Resample.auCop p α s * s + 1) * (p + 1))) := by
  obtain ⟨arrP, Kar, harr⟩ := auSetupArrPipe hk hl
  obtain ⟨lP, Kl, hlPt⟩ := auSetupLPipe hk hl
  obtain ⟨drP, Kdr2, hdr⟩ := auSetupDropPipe hk
  obtain ⟨rcP, Krc, hrc⟩ := auSetupRecsPipe hk hl
  obtain ⟨splitP, Ksp, hsplit⟩ := auSplit hk hl
  obtain ⟨peelP, Kpe, hpeel⟩ := auPeel 1 (by decide)
  obtain ⟨dropP, Kdr, hdrop⟩ := hk.drop
  refine ⟨seqs [arrP, lP, mvVal 0 1 auSplitC auSplitD, drP, pushNil 2, pushNil 3, splitP,
    mvVal 1 0 auSplitC auSplitD, dropP, pushNil 1, rcP, peelP],
    20000 * (Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1), ?_⟩
  intro main p α s t u rest hu hdisc hs hα hp hαp hst
  intro vs a hpre s0 R Bg h0 hk0
  obtain ⟨hvs, ha0⟩ := hpre
  obtain ⟨hsz1, hsz2, hsz3, hsz4, hsz5, hsz6, hsz7, hsz8, hsz9, hsz10, hsz11, hsz12, hsz13⟩ :=
    auSetup_szBd p α s t u hs hα hp hαp hst hu hdisc
  set Bd : ℕ := auSetupBd p α s t with hBd
  set BIG : ℕ := 1000 * (Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1) * Bd with hBIG
  obtain ⟨hBs, hBcs, hBt, hBp, hB1⟩ := auSetupBd_ge p α s t (by omega)
  rw [← hBd] at hBs hBcs hBt hBp hB1
  have htw : 1 ≤ t := by omega
  have hKsp : Ksp ≤ Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1 := by omega
  have hKpe : Kpe ≤ Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1 := by omega
  have hKdr : Kdr ≤ Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1 := by omega
  have hKar : Kar ≤ Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1 := by omega
  have hKl : Kl ≤ Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1 := by omega
  have hKdr2 : Kdr2 ≤ Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1 := by omega
  have hKrc : Krc ≤ Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1 := by omega
  have hKs1 : 1 ≤ Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1 := by omega
  -- stage 1: build the extended array on the value stack
  have hst1 : s0.stk 0 = encs ((ofList (auSetupInp u) :: auPvals p α s t) ++ rest) ++ R := by
    rw [h0, hvs]
    simp only [auSetupInp]
  have harrP : Pipe main arrP (ofList (auSetupInp u) :: auPvals p α s t)
      (ofList (auSetupE p α s u) :: auPvals p α s t) (Kar * auSetupBd p α s t) :=
    harr main p α s t u hu hdisc hs hα hp hαp hst
  obtain ⟨s1, n1, hev1, hn1, hs1, hf1⟩ := pipe_state harrP s0 hst1
  have he1 : Ev main arrP s0 s1 BIG := hev1.mono (C' := BIG) (by
    have h := hn1
    rw [← hBd] at h
    rw [hBIG]
    nlinarith [h, hKar, hKs1])
  -- stage 2: read the window length off the table
  have hlP' : Pipe main lP (ofList (auSetupE p α s u) :: auPvals p α s t)
      (Val.int (auL p α : ℤ) :: ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
        :: ofList (auSetupE p α s u) :: auPvals p α s t) (Kl * auSetupBd p α s t) :=
    hlPt main p α s t u hu hdisc hs hα hp hαp hst
  obtain ⟨s2, n2, hev2, hn2, hs2, hf2⟩ := pipe_state hlP' s1 hs1
  have he2 : Ev main lP s1 s2 BIG := hev2.mono (C' := BIG) (by
    have h := hn2
    rw [← hBd] at h
    rw [hBIG]
    nlinarith [h, hKl, hKs1])
  -- stage 3: move `int L` to stack 1
  have hstw : s2.stk 0 = (Val.int (auL p α : ℤ)).enc ++
      (encs ((ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
        :: ofList (auSetupE p α s u) :: auPvals p α s t) ++ rest) ++ R) := by
    rw [hs2]
    simp only [Work.Kernel.encs_append, Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s3, n3, hev3, hn3, hs3_0, hs3_1, hs3_c, hs3_d, hf3⟩ :=
    mvVal_state (a := 0) (b := 1) (c := auSplitC) (d := auSplitD)
      (by decide : (0 : Stk) ≠ 1) (by decide : (0 : Stk) ≠ auSplitC)
      (by decide : (0 : Stk) ≠ auSplitD) (by decide : (1 : Stk) ≠ auSplitC)
      (by decide : (1 : Stk) ≠ auSplitD) (by decide : auSplitC ≠ auSplitD) s2
      (v := Val.int (auL p α : ℤ))
      (A := encs ((ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
        :: ofList (auSetupE p α s u) :: auPvals p α s t) ++ rest) ++ R)
      (B := s2.stk 1) hstw rfl
  have hs3_1' : s3.stk 1 = encs ([Val.int (auL p α : ℤ)] : List Val) ++ Bg 1 := by
    rw [hs3_1, hf2 1 (by decide), hf1 1 (by decide), hk0 1 (by decide), ha0 1 (by decide)]
    simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.nil_append, List.append_nil]
    try rfl
  have he3 : Ev main (mvVal 0 1 auSplitC auSplitD) s2 s3 BIG := hev3.mono (C' := BIG) (by
    have h := hn3
    rw [Work.ConvR.vsz_int] at h
    rw [hBIG]
    nlinarith [h, hsz5, hKs1])
  -- stage 4: drop the two auxiliary lists
  have hdr' : Pipe main drP (ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
      :: ofList (auSetupE p α s u) :: auPvals p α s t)
      (ofList (auSetupE p α s u) :: auPvals p α s t) (Kdr2 * auSetupBd p α s t) :=
    hdr main p α s t u hu hdisc hs hα hp hαp hst
  obtain ⟨s4, n4, hev4, hn4, hs4, hf4⟩ := pipe_state hdr' s3 hs3_0
  have he4 : Ev main drP s3 s4 BIG := hev4.mono (C' := BIG) (by
    have h := hn4
    rw [← hBd] at h
    rw [hBIG]
    nlinarith [h, hKdr2, hKs1])
  -- stage 5: the sentinel on stack 2
  obtain ⟨s5, n5, hev5, hn5, hs5_2, hf5⟩ := pushNil_ev main 2 s4
  have hs5_2' : s5.stk 2 = encs ([Val.nil] : List Val) ++ Bg 2 := by
    rw [hs5_2, hf4 2 (by decide), hf3 2 (by decide) (by decide) (by decide) (by decide),
      hf2 2 (by decide), hf1 2 (by decide), hk0 2 (by decide), ha0 2 (by decide)]
    simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.nil_append, List.append_nil]
    try rfl
  have he5 : Ev main (pushNil 2) s4 s5 BIG := hev5.mono (C' := BIG) (by
    rw [hBIG]; nlinarith [hKs1, hB1])
  -- stage 6: the sentinel on stack 3
  obtain ⟨s6, n6, hev6, hn6, hs6_3, hf6⟩ := pushNil_ev main 3 s5
  have hs6_3' : s6.stk 3 = encs ([Val.nil] : List Val) ++ Bg 3 := by
    rw [hs6_3, hf5 3 (by decide), hf4 3 (by decide),
      hf3 3 (by decide) (by decide) (by decide) (by decide),
      hf2 3 (by decide), hf1 3 (by decide), hk0 3 (by decide), ha0 3 (by decide)]
    simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.nil_append, List.append_nil]
    try rfl
  have he6 : Ev main (pushNil 3) s5 s6 BIG := hev6.mono (C' := BIG) (by
    rw [hBIG]; nlinarith [hKs1, hB1])
  -- the description used by the split
  set d3 : Stk → List Val := Function.update (Function.update
    (Function.update a 1 [Val.int (auL p α : ℤ)]) 2 [Val.nil]) 3 [Val.nil] with hd3
  have hd3_1 : d3 1 = [Val.int (auL p α : ℤ)] := by simp [hd3]
  have hd3_2 : d3 2 = [Val.nil] := by simp [hd3]
  have hd3_3 : d3 3 = [Val.nil] := by simp [hd3]
  have hd3_a : ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → d3 k = a k := by
    intro k h0k h1k h2k h3k
    simp only [hd3, Function.update_apply, if_neg h1k, if_neg h2k, if_neg h3k]
  have hd3_frame : ∀ k, k ≠ 0 → s6.stk k = encs (d3 k) ++ Bg k := by
    intro k hk
    by_cases h1 : k = 1
    · subst h1
      rw [hf6 1 (by decide), hf5 1 (by decide), hf4 1 (by decide), hs3_1', hd3_1]
    · by_cases h2 : k = 2
      · subst h2
        rw [hf6 2 (by decide), hs5_2', hd3_2]
      · by_cases h3 : k = 3
        · subst h3
          rw [hs6_3', hd3_3]
        · have hs63 : s6.stk k = s3.stk k := by rw [hf6 k h3, hf5 k h2, hf4 k hk]
          have hs30 : s3.stk k = s0.stk k := by
            by_cases hc : k = auSplitC
            · rw [hc, hs3_c, hf2 auSplitC (by decide), hf1 auSplitC (by decide)]
            · by_cases hd : k = auSplitD
              · rw [hd, hs3_d, hf2 auSplitD (by decide), hf1 auSplitD (by decide)]
              · rw [hf3 k hk h1 hc hd, hf2 k hk, hf1 k hk]
          rw [hs63, hs30, hk0 k hk, hd3_a k hk h1 h2 h3]
  -- stage 7: the split
  have hs6_0 : s6.stk 0 = encs ((ofList (auSetupE p α s u) :: auPvals p α s t) ++ rest) ++ R := by
    rw [hf6 0 (by decide), hf5 0 (by decide), hs4]
  obtain ⟨out7, b7, s7, n7, hpost7, hev7, hn7, hs7_0, hs7_fr⟩ :=
    hsplit main (auL p α) (auSetupE p α s u) (auPvals p α s t ++ rest)
      (ofList (auSetupE p α s u) :: (auPvals p α s t ++ rest)) d3
      ⟨rfl, hd3_1, hd3_2⟩ s6 R Bg hs6_0 hd3_frame
  obtain ⟨hs7_out, hb7_1, hb7_2, hb7_oth⟩ := hpost7
  have he7 : Ev main splitP s6 s7 BIG := ⟨n7, hev7, by
    have h := hn7
    rw [hBIG]
    nlinarith [h, hsz7, hsz5, hKsp, hKs1, hB1]⟩
  -- stage 8: move `int L` back to the value stack
  have hs7_1 : s7.stk 1 = (Val.int (auL p α : ℤ)).enc ++ Bg 1 := by
    rw [hs7_fr 1 (by decide), hb7_1]
    simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.nil_append, List.append_nil]
    try rfl
  obtain ⟨s8, n8, hev8, hn8, hs8_1, hs8_0, hs8_c, hs8_d, hf8⟩ :=
    mvVal_state (a := 1) (b := 0) (c := auSplitC) (d := auSplitD)
      (by decide : (1 : Stk) ≠ 0) (by decide : (1 : Stk) ≠ auSplitC)
      (by decide : (1 : Stk) ≠ auSplitD) (by decide : (0 : Stk) ≠ auSplitC)
      (by decide : (0 : Stk) ≠ auSplitD) (by decide : auSplitC ≠ auSplitD) s7
      (v := Val.int (auL p α : ℤ)) (A := Bg 1) (B := s7.stk 0) hs7_1 rfl
  have hs8_1' : s8.stk 1 = encs ([] : List Val) ++ Bg 1 := by
    rw [hs8_1, Work.Kernel.encs_nil, List.nil_append]
  have he8 : Ev main (mvVal 1 0 auSplitC auSplitD) s7 s8 BIG := hev8.mono (C' := BIG) (by
    have h := hn8
    rw [Work.ConvR.vsz_int] at h
    rw [hBIG]
    nlinarith [h, hsz5, hKs1])
  -- stage 9: drop the `int L` again
  obtain ⟨out9, s9, n9, hpost9, hev9, hn9, hs9_0, hf9⟩ :=
    hdrop main (Val.int (auL p α : ℤ) :: (ofList ((auSetupE p α s u).take (auL p α))
        :: (auPvals p α s t ++ rest))) (by simp) s8 R (by
      simp only [hs8_0, hs7_0, hs7_out, Work.Kernel.encs_cons, List.append_assoc])
  obtain ⟨v9, r9, hv9, hout9⟩ := hpost9
  have hr9 : r9 = ofList ((auSetupE p α s u).take (auL p α)) :: (auPvals p α s t ++ rest) := by
    have hcomp : v9 :: r9 = Val.int (auL p α : ℤ)
        :: (ofList ((auSetupE p α s u).take (auL p α)) :: (auPvals p α s t ++ rest)) := hv9.symm
    exact (List.cons.inj hcomp).2
  have hs9_0' : s9.stk 0 = encs ((ofList ((auSetupE p α s u).take (auL p α))
      :: auPvals p α s t) ++ rest) ++ R := by
    rw [hs9_0, hout9, hr9]
    rfl
  have hn9' : n9 ≤ Kdr * (vsz (Val.int (auL p α : ℤ)) + 1) := by
    simpa only [List.headD_cons] using hn9
  have he9 : Ev main dropP s8 s9 BIG := ⟨n9, hev9, by
    have h := hn9'
    rw [Work.ConvR.vsz_int] at h
    rw [hBIG]
    nlinarith [h, hsz5, hKdr, hKs1]⟩
  -- stage 10: the sentinel on stack 1
  obtain ⟨s10, n10, hev10, hn10, hs10_1, hf10⟩ := pushNil_ev main 1 s9
  have hs10_1' : s10.stk 1 = encs ([Val.nil] : List Val) ++ Bg 1 := by
    rw [hs10_1, hf9 1 (by decide), hs8_1']
    simp only [Work.Kernel.encs_cons, Work.Kernel.encs_nil, List.nil_append, List.append_nil]
    try rfl
  have he10 : Ev main (pushNil 1) s9 s10 BIG := hev10.mono (C' := BIG) (by
    rw [hBIG]; nlinarith [hKs1, hB1])
  -- stage 11: the record run
  have hrc' : Pipe main rcP (ofList ((auSetupE p α s u).take (auL p α)) :: auPvals p α s t)
      (ofList ((auRecsF p α s t).reverse) :: ofList ((auSetupE p α s u).take (auL p α))
        :: auPvals p α s t) (Krc * auSetupBd p α s t) :=
    hrc main p α s t u (ofList ((auSetupE p α s u).take (auL p α))) hu hdisc hs hα hp hαp hst hsz8
  obtain ⟨s11, n11, hev11, hn11, hs11, hf11⟩ := pipe_state hrc' s10 (by
      rw [hf10 0 (by decide), hs9_0'])
  have he11 : Ev main rcP s10 s11 BIG := hev11.mono (C' := BIG) (by
    have h := hn11
    rw [← hBd] at h
    rw [hBIG]
    nlinarith [h, hKrc, hKs1])
  -- stage 12: the peel onto stack 1
  set d10 : Stk → List Val := Function.update (Function.update b7 1 []) 1 [Val.nil] with hd10
  have hd10_1 : d10 1 = [Val.nil] := by simp [hd10]
  have hd10_2 : d10 2 = b7 2 := by simp [hd10]
  have hd10_3 : d10 3 = b7 3 := by simp [hd10]
  have hd10_k : ∀ k, k ≠ 1 → d10 k = b7 k := by
    intro k hk
    rw [hd10]; simp [Function.update_of_ne hk]
  have hd10_frame : ∀ k, k ≠ 0 → s10.stk k = encs (d10 k) ++ Bg k := by
    intro k hk
    by_cases h1 : k = 1
    · subst h1
      rw [hd10_1, hs10_1']
    · rw [hd10_k k h1]
      have hs87 : s8.stk k = s7.stk k := by
        by_cases hc : k = auSplitC
        · rw [hc]; exact hs8_c
        · by_cases hd : k = auSplitD
          · rw [hd]; exact hs8_d
          · exact hf8 k h1 hk hc hd
      rw [hf10 k h1, hf9 k hk, hs87, hs7_fr k hk]
  have hd10_frame11 : ∀ k, k ≠ 0 → s11.stk k = encs (d10 k) ++ Bg k := by
    intro k hk
    rw [hf11 k hk]
    exact hd10_frame k hk
  have hst12 : s11.stk 0 = encs (ofList ((auRecsF p α s t).reverse)
      :: ((ofList ((auSetupE p α s u).take (auL p α)) :: auPvals p α s t) ++ rest)) ++ R := by
    rw [hs11]; rfl
  obtain ⟨out12, b12, s12, n12, hpost12, hev12, hn12, hs12_0, hs12_fr⟩ :=
    hpeel main ((auRecsF p α s t).reverse)
      ((ofList ((auSetupE p α s u).take (auL p α)) :: auPvals p α s t) ++ rest)
      Val.nil (ofList ((auRecsF p α s t).reverse)
        :: ((ofList ((auSetupE p α s u).take (auL p α)) :: auPvals p α s t) ++ rest)) d10
      ⟨rfl, hd10_1⟩ s11 R Bg hst12 hd10_frame11
  obtain ⟨hb12_out, hb12_a, hb12_1, hb12_oth⟩ := hpost12
  have he12 : Ev main peelP s11 s12 BIG := ⟨n12, hev12, by
    have h := hn12
    have h1 : vsz (ofList ((auRecsF p α s t).reverse)) = vsz (ofList (auRecsF p α s t)) :=
      vsz_ofList_reverse _
    rw [h1] at h
    rw [hBIG]
    nlinarith [h, hsz13, hKpe, hKs1, hB1]⟩
  -- the chain of stages
  have E12 : Ev main peelP s11 s12 BIG := he12
  have E11 : Ev main (Cmd.seq rcP peelP) s10 s12 (2 * BIG) :=
    Ev.seq' he11 E12 (by omega)
  have E10 : Ev main (Cmd.seq (pushNil 1) (Cmd.seq rcP peelP)) s9 s12 (3 * BIG) :=
    Ev.seq' he10 E11 (by omega)
  have E9 : Ev main (Cmd.seq dropP (Cmd.seq (pushNil 1) (Cmd.seq rcP peelP))) s8 s12 (4 * BIG) :=
    Ev.seq' he9 E10 (by omega)
  have E8 : Ev main (Cmd.seq (mvVal 1 0 auSplitC auSplitD)
      (Cmd.seq dropP (Cmd.seq (pushNil 1) (Cmd.seq rcP peelP)))) s7 s12 (5 * BIG) :=
    Ev.seq' he8 E9 (by omega)
  have E7 : Ev main (Cmd.seq splitP (Cmd.seq (mvVal 1 0 auSplitC auSplitD)
      (Cmd.seq dropP (Cmd.seq (pushNil 1) (Cmd.seq rcP peelP))))) s6 s12 (6 * BIG) :=
    Ev.seq' he7 E8 (by omega)
  have E6 : Ev main (Cmd.seq (pushNil 3) (Cmd.seq splitP (Cmd.seq (mvVal 1 0 auSplitC auSplitD)
      (Cmd.seq dropP (Cmd.seq (pushNil 1) (Cmd.seq rcP peelP)))))) s5 s12 (7 * BIG) :=
    Ev.seq' he6 E7 (by omega)
  have E5 : Ev main (Cmd.seq (pushNil 2) (Cmd.seq (pushNil 3) (Cmd.seq splitP
      (Cmd.seq (mvVal 1 0 auSplitC auSplitD) (Cmd.seq dropP (Cmd.seq (pushNil 1)
      (Cmd.seq rcP peelP))))))) s4 s12 (8 * BIG) :=
    Ev.seq' he5 E6 (by omega)
  have E4 : Ev main (Cmd.seq drP (Cmd.seq (pushNil 2) (Cmd.seq (pushNil 3) (Cmd.seq splitP
      (Cmd.seq (mvVal 1 0 auSplitC auSplitD) (Cmd.seq dropP (Cmd.seq (pushNil 1)
      (Cmd.seq rcP peelP)))))))) s3 s12 (9 * BIG) :=
    Ev.seq' he4 E5 (by omega)
  have E3 : Ev main (Cmd.seq (mvVal 0 1 auSplitC auSplitD) (Cmd.seq drP
      (Cmd.seq (pushNil 2) (Cmd.seq (pushNil 3) (Cmd.seq splitP
      (Cmd.seq (mvVal 1 0 auSplitC auSplitD) (Cmd.seq dropP (Cmd.seq (pushNil 1)
      (Cmd.seq rcP peelP))))))))) s2 s12 (10 * BIG) :=
    Ev.seq' he3 E4 (by omega)
  have E2 : Ev main (Cmd.seq lP (Cmd.seq (mvVal 0 1 auSplitC auSplitD) (Cmd.seq drP
      (Cmd.seq (pushNil 2) (Cmd.seq (pushNil 3) (Cmd.seq splitP
      (Cmd.seq (mvVal 1 0 auSplitC auSplitD) (Cmd.seq dropP (Cmd.seq (pushNil 1)
      (Cmd.seq rcP peelP)))))))))) s1 s12 (11 * BIG) :=
    Ev.seq' he2 E3 (by omega)
  have E1 : Ev main (seqs [arrP, lP, mvVal 0 1 auSplitC auSplitD, drP, pushNil 2, pushNil 3, splitP,
      mvVal 1 0 auSplitC auSplitD, dropP, pushNil 1, rcP, peelP]) s0 s12 (12 * BIG) :=
    Ev.seq' he1 E2 (by omega)
  obtain ⟨N, hevN, hleN⟩ := E1
  have hcost : N ≤ 20000 * (Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1) *
      ((s + t * auL p α + auCop p α s * s + 1) * (p + 1)) := by
    have h1 : 12 * BIG ≤ 20000 * (Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1) *
        ((s + t * auL p α + auCop p α s * s + 1) * (p + 1)) := by
      rw [hBIG, hBd, auSetupBd_def]
      have h2 : 12 * (1000 * (Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1) *
          ((s + t * auL p α + auCop p α s * s + 1) * (p + 1)))
          = 12000 * ((Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1) *
              ((s + t * auL p α + auCop p α s * s + 1) * (p + 1))) := by ring
      have h3 : (20000 * (Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1)) *
          ((s + t * auL p α + auCop p α s * s + 1) * (p + 1))
          = 20000 * ((Kar + Kl + Kdr2 + Krc + Ksp + Kpe + Kdr + 1) *
              ((s + t * auL p α + auCop p α s * s + 1) * (p + 1))) := by ring
      rw [h2, h3]
      exact Nat.mul_le_mul_right _ (by omega : 12000 ≤ 20000)
    exact le_trans hleN h1
  -- the description of the final value stack and of the final runs
  have hval : ofList ((auSetupE p α s u).take (auL p α)) = ofList (auWinV p α s t u 0) := by
    rw [auWinV_zero p α s t u hs hu (by omega)]
  set bfin : Stk → List Val := Function.update
    (Function.update (Function.update a 1 (auRecsF p α s t ++ [Val.nil]))
      2 (auElems p α s u ++ [Val.nil])) 3 [Val.nil] with hbfin
  have hb1 : bfin 1 = auRecsF p α s t ++ [Val.nil] := by
    rw [hbfin, Function.update_of_ne (by decide : (1 : Stk) ≠ 3),
      Function.update_of_ne (by decide : (1 : Stk) ≠ 2), Function.update_self]
  have hb2 : bfin 2 = auElems p α s u ++ [Val.nil] := by
    rw [hbfin, Function.update_of_ne (by decide : (2 : Stk) ≠ 3), Function.update_self]
  have hb3 : bfin 3 = [Val.nil] := by
    rw [hbfin, Function.update_self]
  have hbk : ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → bfin k = a k := by
    intro k h0k h1k h2k h3k
    rw [hbfin, Function.update_of_ne h3k, Function.update_of_ne h2k, Function.update_of_ne h1k]
  refine ⟨ofList (auWinV p α s t u 0) :: auPvals p α s t ++ rest, bfin, s12, N,
    ⟨?_, ?_, ?_, ?_, ?_⟩, hevN, hcost, ?_, ?_⟩
  · rfl
  · exact hb1
  · exact hb2
  · exact hb3
  · exact hbk
  · rw [hs12_0, hb12_out, hval]
  · intro k hk
    by_cases h1 : k = 1
    · subst h1
      rw [hb1, hs12_fr 1 (by decide), hb12_1, List.reverse_reverse]
    · by_cases h2 : k = 2
      · subst h2
        rw [hb2, hs12_fr 2 (by decide), hb12_oth 2 (by decide) (by decide), hd10_2, hb7_2,
          auSetupE_drop p α s u]
      · by_cases h3 : k = 3
        · subst h3
          rw [hb3, hs12_fr 3 (by decide), hb12_oth 3 (by decide) (by decide), hd10_3,
            hb7_oth 3 (by decide) (by decide) (by decide), hd3_3]
        · rw [hbk k hk h1 h2 h3, hs12_fr k hk, hb12_oth k hk h1, hd10_k k h1,
            hb7_oth k hk h1 h2, hd3_a k hk h1 h2 h3]

end Work.Resample
