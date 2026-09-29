import Submission.Work.Compiler.SimSteps

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Compiler

open HvdH Turing StateTransition

theorem labOf_lab (code : List Instr) (l₂ : ℕ) {l₁ : ℕ} (h₁ : l₁ ≤ code.length)
    (h : l₁ = l₂) : labOf code l₁ h₁ = lab code l₂ := by
  rw [(lab_mk code h₁).symm, h]

theorem list_map_id {α : Type*} (l : List α) : List.map id l = l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, ih]; rfl

theorem toStk_of_stk_eq {code : List Instr} {s t : State} (h : s.stk = t.stk)
    (L0 : List InSym) (L1 : List Bool) (rs : List (Λ code)) :
    toStk code s L0 L1 rs = toStk code t L0 L1 rs := by
  funext j
  cases j with
  | inl k => simp [toStk, congrFun h k]
  | inr j => fin_cases j <;> simp [toStk]

/-- The final `ret` of the whole program, with an empty return stack. -/
def eit_ret_none (code : List Instr) (p : ℕ) (hp : p ≤ code.length)
    (hk : code[p]? = some Instr.ret) (σ : MS code) (s : State)
    (L0 : List InSym) (L1 : List Bool) :
    EIT code ⟨some (labOf code p hp), σ, toStk code s L0 L1 []⟩
      ⟨some (labE1 code), ⟨σ.reg, σ.dat, σ.sym, none⟩, toStk code s L0 L1 []⟩ 1 := by
  have hk' : code[((labOf code p hp : Λ code) : ℕ)]? = some Instr.ret := hk
  have hl : ((toStk code s L0 L1 ([] : List (Λ code))) (Sum.inr 2)).head? = none := rfl
  refine eit_one ?_
  rw [step_ret_none code (labOf code p hp) hk' σ (toStk code s L0 L1 []) hl]
  try rfl

/-- **Simulation.**  The compiled block of `c` (at position `pc` of `code`) takes the machine from
the configuration with registers `σ.reg` and stacks `toStk code s L0 L1 rs` to the configuration at
position `pc + clen c` with the language stacks of `s'` and the same return stack, in `≤ 10 * n`
steps. -/
theorem simulate (code : List Instr) (main : Cmd) (hmain : CodeAt code 0 main)
    (hret : code[clen main]? = some Instr.ret) :
    ∀ {c : Cmd} {s s' : State} {n : ℕ}, Eval main c s s' n →
      ∀ (pc : ℕ) (hpc : pc ≤ code.length) (hZ : pc + clen c ≤ code.length)
        (hc : CodeAt code pc c) (σ : MS code) (L0 : List InSym) (L1 : List Bool)
        (rs : List (Λ code)), σ.reg = s.reg →
      ∃ σ' : MS code, σ'.reg = s'.reg ∧
        Nonempty (EIT code
          ⟨some (labOf code pc hpc), σ, toStk code s L0 L1 rs⟩
          ⟨some (labOf code (pc + clen c) hZ), σ', toStk code s' L0 L1 rs⟩
          (10 * n)) := by
  intro c s s' n h
  induction h with
  | skip s =>
      intro pc hpc hZ hc σ L0 L1 rs hreg
      have hp1 : pc + 1 ≤ code.length := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hc).choose
      exact ⟨σ, hreg, ⟨eit_mono (eit_skip code pc hpc hp1 hc σ s L0 L1 rs) (by norm_num)⟩⟩
  | pop k r s =>
      intro pc hpc hZ hc σ L0 L1 rs hreg
      have hp1 : pc + 1 ≤ code.length := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hc).choose
      refine ⟨{σ with reg := Function.update σ.reg r ((s.stk k).head?.getD Glyph.eos)}, ?_, ?_⟩
      · show Function.update σ.reg r ((s.stk k).head?.getD Glyph.eos)
            = Function.update s.reg r ((s.stk k).headD Glyph.eos)
        rw [hreg, List.headD_eq_head?_getD]
      · exact ⟨eit_mono (eit_pop code pc hpc hp1 k r hc σ s L0 L1 rs) (by norm_num)⟩
  | peek k r s =>
      intro pc hpc hZ hc σ L0 L1 rs hreg
      have hp1 : pc + 1 ≤ code.length := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hc).choose
      refine ⟨{σ with reg := Function.update σ.reg r ((s.stk k).head?.getD Glyph.eos)}, ?_, ?_⟩
      · show Function.update σ.reg r ((s.stk k).head?.getD Glyph.eos)
            = Function.update s.reg r ((s.stk k).headD Glyph.eos)
        rw [hreg, List.headD_eq_head?_getD]
      · exact ⟨eit_mono (eit_peek code pc hpc hp1 k r hc σ s L0 L1 rs) (by norm_num)⟩
  | push k r s =>
      intro pc hpc hZ hc σ L0 L1 rs hreg
      have hp1 : pc + 1 ≤ code.length := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hc).choose
      have hr := congrFun hreg r
      exact ⟨σ, hreg, ⟨eit_mono (eit_push code pc hpc hp1 k r hc σ s L0 L1 rs hr) (by norm_num)⟩⟩
  | set r g s =>
      intro pc hpc hZ hc σ L0 L1 rs hreg
      have hp1 : pc + 1 ≤ code.length := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hc).choose
      refine ⟨{σ with reg := Function.update σ.reg r g}, ?_, ?_⟩
      · show Function.update σ.reg r g = Function.update s.reg r g
        rw [hreg]
      · exact ⟨eit_mono (eit_set code pc hpc hp1 r g hc σ s L0 L1 rs) (by norm_num)⟩
  | mov d t s =>
      intro pc hpc hZ hc σ L0 L1 rs hreg
      have hp1 : pc + 1 ≤ code.length := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hc).choose
      have hrt := congrFun hreg t
      refine ⟨{σ with reg := Function.update σ.reg d (s.reg t)}, ?_, ?_⟩
      · show Function.update σ.reg d (s.reg t) = Function.update s.reg d (s.reg t)
        rw [hreg]
      · exact ⟨eit_mono (eit_mov code pc hpc hp1 d t hc σ s L0 L1 rs hrt) (by norm_num)⟩
  | seq h1 h2 ih1 ih2 =>
      rename_i p q s0 s1 s2 n1 n2
      intro pc hpc hZ hc σ L0 L1 rs hreg
      obtain ⟨hc1, hc2⟩ := hc
      obtain ⟨σ1, hreg1, hE1⟩ := ih1 pc hpc (codeAt_le code p pc hc1) hc1 σ L0 L1 rs hreg
      obtain ⟨hE1⟩ := hE1
      obtain ⟨σ2, hreg2, hE2⟩ := ih2 (pc + clen p) (codeAt_le code p pc hc1)
        (codeAt_le code q (pc + clen p) hc2) hc2 σ1 L0 L1 rs hreg1
      obtain ⟨hE2⟩ := hE2
      refine ⟨σ2, hreg2, ?_⟩
      rw [show labOf code (pc + clen (p.seq q)) hZ
            = labOf code ((pc + clen p) + clen q) (codeAt_le code q (pc + clen p) hc2) from
          labOf_congr code hZ _ (by simp only [clen]; omega)]
      exact ⟨eit_mono (eit_trans hE1 hE2) (by omega)⟩
  | iteT hr h1 ih =>
      rename_i r g p q s0 s1 n0
      intro pc hpc hZ hc σ L0 L1 rs hreg
      obtain ⟨hk, hcp, hj, hcq⟩ := hc
      have hv : σ.reg r = g := by rw [congrFun hreg r]; exact hr
      have hp1 : pc + 1 ≤ code.length := codeAt_le_start hcp
      have hp2 : pc + clen p + 1 ≤ code.length := le_of_lt (List.getElem?_eq_some_iff.mp hj).choose
      have hq2 : pc + clen p + 2 + clen q ≤ code.length := codeAt_le code q (pc + clen p + 2) hcq
      have htest := eit_test_true code pc hpc hp1 r g (pc + clen p + 2) hk σ s0 L0 L1 rs hv
      obtain ⟨σ1, hreg1, hE1⟩ := ih (pc + 1) hp1 (codeAt_le code p (pc + 1) hcp) hcp σ L0 L1 rs hreg
      obtain ⟨hE1⟩ := hE1
      rw [show labOf code ((pc + 1) + clen p) (codeAt_le code p (pc + 1) hcp)
            = labOf code (pc + clen p + 1) hp2 from labOf_congr code _ hp2 (by omega)] at hE1
      have hjmp := eit_jmp code (pc + clen p + 1) hp2 (pc + clen p + 2 + clen q) hq2 hj σ1 s1 L0 L1 rs
      refine ⟨σ1, hreg1, ?_⟩
      rw [show labOf code (pc + clen (Cmd.ite r g p q)) hZ
            = labOf code (pc + clen p + 2 + clen q) hq2 from
          labOf_congr code hZ _ (by simp only [clen]; omega)]
      exact ⟨eit_mono (eit_trans (eit_trans htest hE1) hjmp) (by omega)⟩
  | iteF hr h1 ih =>
      rename_i r g p q s0 s1 n0
      intro pc hpc hZ hc σ L0 L1 rs hreg
      obtain ⟨hk, hcp, hj, hcq⟩ := hc
      have hv : σ.reg r ≠ g := fun hh => hr (by rw [← congrFun hreg r]; exact hh)
      have hq1 : pc + clen p + 2 ≤ code.length := codeAt_le_start hcq
      have htest := eit_test_false code pc hpc r g (pc + clen p + 2) hq1 hk σ s0 L0 L1 rs hv
      obtain ⟨σ1, hreg1, hE1⟩ := ih (pc + clen p + 2) hq1
        (codeAt_le code q (pc + clen p + 2) hcq) hcq σ L0 L1 rs hreg
      obtain ⟨hE1⟩ := hE1
      refine ⟨σ1, hreg1, ?_⟩
      rw [show labOf code (pc + clen (Cmd.ite r g p q)) hZ
            = labOf code ((pc + clen p + 2) + clen q) (codeAt_le code q (pc + clen p + 2) hcq) from
          labOf_congr code hZ _ (by simp only [clen]; omega)]
      exact ⟨eit_mono (eit_trans htest hE1) (by omega)⟩
  | loopF hr =>
      rename_i r g b s0
      intro pc hpc hZ hc σ L0 L1 rs hreg
      obtain ⟨hk, hcb, hj⟩ := hc
      have hv : σ.reg r ≠ g := fun hh => hr (by rw [← congrFun hreg r]; exact hh)
      have hZ2 : pc + clen b + 2 ≤ code.length := by simp only [clen] at hZ; omega
      refine ⟨σ, hreg, ?_⟩
      rw [show labOf code (pc + clen (Cmd.loop r g b)) hZ = labOf code (pc + clen b + 2) hZ2 from
          labOf_congr code hZ _ (by simp only [clen]; omega)]
      exact ⟨eit_mono (eit_test_false code pc hpc r g (pc + clen b + 2) hZ2 hk σ s0 L0 L1 rs hv)
        (by norm_num)⟩
  | loopT hr h1 h2 ih1 ih2 =>
      rename_i r g b s0 s1 s2 n0 m0
      intro pc hpc hZ hc σ L0 L1 rs hreg
      have hk := hc.1
      have hcb := hc.2.1
      have hj := hc.2.2
      have hv : σ.reg r = g := by rw [congrFun hreg r]; exact hr
      have hp1 : pc + 1 ≤ code.length := codeAt_le_start hcb
      have hj1 : pc + clen b + 1 ≤ code.length := le_of_lt (List.getElem?_eq_some_iff.mp hj).choose
      have htest := eit_test_true code pc hpc hp1 r g (pc + clen b + 2) hk σ s0 L0 L1 rs hv
      obtain ⟨σ1, hreg1, hE1⟩ := ih1 (pc + 1) hp1 (codeAt_le code b (pc + 1) hcb) hcb σ L0 L1 rs hreg
      obtain ⟨hE1⟩ := hE1
      rw [show labOf code ((pc + 1) + clen b) (codeAt_le code b (pc + 1) hcb)
            = labOf code (pc + clen b + 1) hj1 from labOf_congr code _ hj1 (by omega)] at hE1
      have hjmp := eit_jmp code (pc + clen b + 1) hj1 pc hpc hj σ1 s1 L0 L1 rs
      obtain ⟨σ2, hreg2, hE2⟩ := ih2 pc hpc hZ hc σ1 L0 L1 rs hreg1
      obtain ⟨hE2⟩ := hE2
      exact ⟨σ2, hreg2, ⟨eit_mono (eit_trans (eit_trans (eit_trans htest hE1) hjmp) hE2)
        (by omega)⟩⟩
  | self h1 ih =>
      rename_i s0 s1 n0
      intro pc hpc hZ hc σ L0 L1 rs hreg
      have hP : clen main ≤ code.length :=
        le_of_lt (List.getElem?_eq_some_iff.mp hret).choose
      have hZ0 : 0 + clen main ≤ code.length := by omega
      have hcall := eit_call code pc hpc hc σ s0 L0 L1 rs
      obtain ⟨σ1, hreg1, hE1⟩ := ih 0 (Nat.zero_le _) hZ0 hmain σ L0 L1
        (lab code (pc + 1) :: rs) hreg
      obtain ⟨hE1⟩ := hE1
      rw [show labOf code (0 + clen main) hZ0 = labOf code (clen main) hP from
          labOf_congr code hZ0 hP (by omega)] at hE1
      have hretstep := eit_ret code (clen main) hP (lab code (pc + 1)) hret σ1 s1 L0 L1 rs
      refine ⟨{σ1 with ret := some (lab code (pc + 1))}, hreg1, ?_⟩
      rw [labOf_lab code (pc + 1) hZ (by rfl)]
      exact ⟨eit_mono (eit_trans (eit_trans hcall hE1) hretstep) (by omega)⟩

end Work.Compiler
