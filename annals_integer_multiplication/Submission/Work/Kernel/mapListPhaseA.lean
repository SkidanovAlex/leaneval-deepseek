import Mathlib
import Submission.Work.Kernel.mapListDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Kernel

open HvdH
open Work.Layout

/-- One `mapList_bodyA` iteration when the top glyph of stack 0 is `cons`: the `cons` cell is popped
and the exposed element moved to stack 1. -/
theorem mapList_bodyA_cons {main : Cmd} {s : State} {x : Val} {A₁ : List Glyph}
    (h0 : s.stk 0 = Glyph.cons :: (x.enc ++ A₁)) :
    ∃ (s' : State) (C : ℕ), Ev main mapList_bodyA s s' C ∧ C ≤ 16 * (vsz x + 1) + 4 ∧
      s'.stk 0 = A₁ ∧ s'.stk 1 = x.enc ++ s.stk 1 ∧ s'.reg rLoopG = Glyph.cons ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  have hhead : (s.stk 0).headD Glyph.eos = Glyph.cons := by rw [h0]; rfl
  set sp : State := ⟨Function.update s.reg rA ((s.stk 0).headD Glyph.eos), s.stk⟩ with hsp
  have hpeek : Ev main (.peek 0 rA) s sp 1 := by rw [hsp]; exact ev_peek main 0 rA s
  have hsp_reg : sp.reg rA = Glyph.cons := by
    rw [hsp]; simpa only [Function.update_self] using hhead
  have hsp_reg_ne : sp.reg rA ≠ Glyph.nil := by rw [hsp_reg]; exact gcons_ne_nil
  set sq : State := State.tPop sp 0 rA with hsq
  have hpop : Ev main (.pop 0 rA) sp sq 1 := by rw [hsq]; exact ev_pop main 0 rA sp
  have hsq0 : sq.stk 0 = x.enc ++ A₁ := by
    rw [hsq]; simp [State.tPop, hsp, h0]
  have hsq1 : sq.stk 1 = s.stk 1 := by
    rw [hsq]; simp [State.tPop, hsp]
  have hsqk : ∀ j : Stk, j ≠ 0 → sq.stk j = s.stk j := by
    intro j hj
    rw [hsq]; simp [State.tPop, hsp, hj]
  obtain ⟨s₂, n₂, hmv, hn₂, h20, h21, h24, h25, hf₂⟩ :=
    mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 4) (d := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := sq.reg) (X := sq.stk) (v := x) (A := A₁) (B := s.stk 1) hsq0 hsq1
  set sr : State := State.tSet s₂ rLoopG Glyph.cons with hsr
  have hset : Ev main (.set rLoopG Glyph.cons) s₂ sr 1 := by
    rw [hsr]; exact ev_set main rLoopG Glyph.cons s₂
  have hs20 : sr.stk 0 = A₁ := by rw [hsr]; simpa [State.tSet, State.updReg] using h20
  have hs21 : sr.stk 1 = x.enc ++ s.stk 1 := by
    rw [hsr]; simpa [State.tSet, State.updReg] using h21
  have hs2r : sr.reg rLoopG = Glyph.cons := by rw [hsr]; rfl
  have hsr_stk : ∀ k : Stk, sr.stk k = s₂.stk k := by
    intro k; rw [hsr]; rfl
  have hfr : ∀ k : Stk, k ≠ 0 → k ≠ 1 → sr.stk k = s.stk k := by
    intro k hk0 hk1
    rw [hsr_stk k]
    rcases eq_or_ne k 4 with h4 | h4
    · subst h4; rw [h24, hsqk 4 (by decide)]
    · rcases eq_or_ne k 5 with h5 | h5
      · subst h5; rw [h25, hsqk 5 (by decide)]
      · rw [hf₂ k hk0 hk1 h4 h5, hsqk k hk0]
  refine ⟨sr, n₂ + 4, ?_, ?_, hs20, hs21, hs2r, hfr⟩
  · have hinner : Ev main (.seq (mvVal 0 1 4 5) (.set rLoopG Glyph.cons)) sq sr (n₂ + 1) :=
      Ev.seq' hmv hset (by omega)
    have hbr : Ev main (.seq (.pop 0 rA) (.seq (mvVal 0 1 4 5) (.set rLoopG Glyph.cons))) sp sr (n₂ + 2) :=
      Ev.seq' hpop hinner (by omega)
    have hite : Ev main (.ite rA Glyph.nil (.seq (.pop 0 rA) (.set rLoopG Glyph.eos))
        (.seq (.pop 0 rA) (.seq (mvVal 0 1 4 5) (.set rLoopG Glyph.cons)))) sp sr (n₂ + 3) :=
      Ev.iteF hsp_reg_ne hbr
    unfold mapList_bodyA
    exact Ev.seq' hpeek hite (by omega)
  · omega

/-- One `mapList_bodyA` iteration when the top glyph of stack 0 is `nil`: pop it and stop. -/
theorem mapList_bodyA_nil {main : Cmd} {s : State} {A₁ : List Glyph}
    (h0 : s.stk 0 = Glyph.nil :: A₁) :
    ∃ (s' : State) (C : ℕ), Ev main mapList_bodyA s s' C ∧ C ≤ 4 ∧
      s'.stk 0 = A₁ ∧ s'.stk 1 = s.stk 1 ∧ s'.reg rLoopG = Glyph.eos ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  have hhead : (s.stk 0).headD Glyph.eos = Glyph.nil := by rw [h0]; rfl
  set sp : State := ⟨Function.update s.reg rA ((s.stk 0).headD Glyph.eos), s.stk⟩ with hsp
  have hpeek : Ev main (.peek 0 rA) s sp 1 := by rw [hsp]; exact ev_peek main 0 rA s
  have hsp_reg : sp.reg rA = Glyph.nil := by
    rw [hsp]; simpa only [Function.update_self] using hhead
  set sq : State := State.tPop sp 0 rA with hsq
  have hpop : Ev main (.pop 0 rA) sp sq 1 := by rw [hsq]; exact ev_pop main 0 rA sp
  have hsq0 : sq.stk 0 = A₁ := by rw [hsq]; simp [State.tPop, hsp, h0]
  have hsqk : ∀ j : Stk, j ≠ 0 → sq.stk j = s.stk j := by
    intro j hj
    rw [hsq]; simp [State.tPop, hsp, hj]
  set sr : State := State.tSet sq rLoopG Glyph.eos with hsr
  have hset : Ev main (.set rLoopG Glyph.eos) sq sr 1 := by
    rw [hsr]; exact ev_set main rLoopG Glyph.eos sq
  have hs0 : sr.stk 0 = A₁ := by rw [hsr]; simpa [State.tSet, State.updReg] using hsq0
  have hs1 : sr.stk 1 = s.stk 1 := by rw [hsr]; simpa [State.tSet, State.updReg, hsqk 1 (by decide)]
  have hsr' : sr.reg rLoopG = Glyph.eos := by rw [hsr]; rfl
  have hsr_stk : ∀ k : Stk, sr.stk k = sq.stk k := by intro k; rw [hsr]; rfl
  have hfr : ∀ k : Stk, k ≠ 0 → k ≠ 1 → sr.stk k = s.stk k := by
    intro k hk0 hk1; rw [hsr_stk k]; exact hsqk k hk0
  refine ⟨sr, 4, ?_, ?_, hs0, hs1, hsr', hfr⟩
  · have hbr : Ev main (.seq (.pop 0 rA) (.set rLoopG Glyph.eos)) sp sr 2 :=
      Ev.seq' hpop hset (by omega)
    have hite : Ev main (.ite rA Glyph.nil (.seq (.pop 0 rA) (.set rLoopG Glyph.eos))
        (.seq (.pop 0 rA) (.seq (mvVal 0 1 4 5) (.set rLoopG Glyph.cons)))) sp sr 3 :=
      Ev.iteT hsp_reg hbr
    unfold mapList_bodyA
    exact Ev.seq' hpeek hite (by omega)
  · omega

set_option maxHeartbeats 1600000 in
/-- **Phase A** of `mapList`: move all elements of the list value on top of stack 0 to stack 1
(reversing them), leaving only `rest` on stack 0. -/
theorem mapList_phaseA (main : Cmd) (ws rest : List Val) (R : List Glyph) (s : State) (L : ℕ)
    (hr : s.reg rLoopG = Glyph.cons) (hsz : ∀ x ∈ ws, vsz x ≤ L)
    (h0 : s.stk 0 = encs (ofList ws :: rest) ++ R) :
    ∃ (s' : State) (C : ℕ),
      loopRuns main rLoopG Glyph.cons mapList_bodyA (ws.length + 1) s s' C ∧
      C ≤ ws.length * (16 * (L + 1) + 5) + 6 ∧
      s'.stk 0 = encs rest ++ R ∧ s'.stk 1 = encs ws.reverse ++ s.stk 1 ∧
      s'.reg rLoopG = Glyph.eos ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = s.stk k) := by
  induction ws generalizing s rest with
  | nil =>
    have h0' : s.stk 0 = Glyph.nil :: (encs rest ++ R) := by
      rw [h0, mapList_encs_ofList_nil, List.cons_append]
    obtain ⟨s', C', hev, hC', hs'0, hs'1, hs'r, hfr'⟩ := mapList_bodyA_nil (main := main) h0'
    refine ⟨s', C' + 1, ?_, ?_, ?_, ?_, hs'r, ?_⟩
    · simpa using loopRuns.one hr hev
    · simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]; omega
    · simpa using hs'0
    · simp only [List.reverse_nil, encs_nil, List.nil_append]; exact hs'1
    · intro k hk0 hk1; exact hfr' k hk0 hk1
  | cons x xs ih =>
    have h0' : s.stk 0 = Glyph.cons :: (x.enc ++ (encs (ofList xs :: rest) ++ R)) := by
      rw [h0, mapList_encs_ofList_cons]; simp [List.append_assoc]
    obtain ⟨s₁, C₁, hev₁, hC₁, hs₁0, hs₁1, hs₁r, hfr₁⟩ :=
      mapList_bodyA_cons (main := main) (A₁ := encs (ofList xs :: rest) ++ R) h0'
    have hC₁' : C₁ ≤ 16 * (L + 1) + 4 := by
      have hx := hsz x (by simp)
      omega
    obtain ⟨s₂, C₂, hrun₂, hC₂, hs₂0, hs₂1, hs₂r, hfr₂⟩ :=
      ih (s := s₁) (rest := rest) hs₁r (fun y hy => hsz y (List.mem_cons_of_mem x hy)) hs₁0
    refine ⟨s₂, (16 * (L + 1) + 4) + C₂ + 1, ?_, ?_, hs₂0, ?_, hs₂r, ?_⟩
    · exact loopRuns.succ' hr (hev₁.mono hC₁') hrun₂ (by omega)
    · have hx := hsz x (by simp)
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · rw [hs₂1, hs₁1, mapList_encs_reverse_cons, List.append_assoc]
    · intro k hk0 hk1; rw [hfr₂ k hk0 hk1]; exact hfr₁ k hk0 hk1

end Work.Kernel
