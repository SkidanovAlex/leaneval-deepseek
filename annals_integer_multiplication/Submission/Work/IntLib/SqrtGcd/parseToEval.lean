import Mathlib
import Submission.Work.IntLib.SqrtGcd.SqrtProg
import Submission.Work.Kernel.Raw

/-!
# Evaluation of `SG.parseTo`

`SG.parseTo dst r rP rF` reads the magnitude bits of the integer value on top of stack 0
(`L.map Glyph.bit`, least significant bit first, followed by the `iend` delimiter) and pushes
them onto stack `dst` **most significant bit first**, while `rP` records the parity of `L`
(starting from `Glyph.bit false`) and the loop flag `rF` runs from `gGo` to `gStop`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH

/-! ## Toggle bookkeeping -/

/-- Value of a bit that starts at `b` and is toggled `n` times. -/
def flipB (b : Bool) (n : ℕ) : Bool := if n % 2 = 0 then b else !b

theorem flipB_zero (b : Bool) : flipB b 0 = b := by simp [flipB]

theorem flipB_succ (b : Bool) (n : ℕ) : flipB b (n + 1) = !flipB b n := by
  unfold flipB
  split_ifs <;> simp_all <;> omega

theorem flipB_not (b : Bool) (n : ℕ) : flipB (!b) n = !flipB b n := by
  unfold flipB
  split_ifs <;> simp_all

theorem flipB_false (n : ℕ) : flipB false n = decide (n % 2 = 1) := by
  unfold flipB
  split_ifs <;> simp_all <;> omega

/-- `SG.toggle rP` flips the bit held in the register `rP`. -/
theorem toggle_bit (main : Cmd) (rP : Reg) (bt : Bool) (s : State)
    (h : s.reg rP = Glyph.bit bt) :
    Eval main (SG.toggle rP) s (s.updReg rP (Glyph.bit (!bt))) 2 := by
  rw [SG.toggle]
  cases bt with
  | false =>
    have hne : ¬ (s.reg rP = Glyph.bit true) := by rw [h]; decide
    exact Eval.iteF hne (Eval.set rP (Glyph.bit true) s)
  | true =>
    exact Eval.iteT h (Eval.set rP (Glyph.bit false) s)

/-! ## One loop iteration -/

/-- One iteration of the parse loop on a bit `b`: the bit is popped from stack 0, pushed on
`dst`, the parity register `rP` is toggled and the loop flag is reset to `gGo`. -/
theorem parseBody_bit (main : Cmd) (dst : Stk) (r rP rF : Reg) (h0 : dst ≠ 0)
    (hrP : r ≠ rP) (hPF : rP ≠ rF) (b bt : Bool) (L' : List Bool) (R : List Glyph)
    (s : State) (hstk : s.stk 0 = Glyph.bit b :: (L'.map Glyph.bit ++ [Glyph.iend] ++ R))
    (hrPv : s.reg rP = Glyph.bit bt) :
    ∃ s₁, Eval main (SG.parseBody dst r rP rF) s s₁ 6 ∧
      s₁.stk 0 = L'.map Glyph.bit ++ [Glyph.iend] ++ R ∧
      s₁.stk dst = Glyph.bit b :: s.stk dst ∧
      s₁.reg rP = Glyph.bit (!bt) ∧ s₁.reg rF = SG.gGo ∧
      (∀ k, k ≠ 0 → k ≠ dst → s₁.stk k = s.stk k) := by
  have h0' : (0 : Stk) ≠ dst := fun h => h0 h.symm
  have hrP' : rP ≠ r := fun h => hrP h.symm
  set s1 : State := State.tPop s 0 r with hs1
  set s2 : State := State.tPush s1 dst r with hs2
  set s3 : State := s2.updReg rP (Glyph.bit (!bt)) with hs3
  set s4 : State := s3.updReg rF SG.gGo with hs4
  have hs1reg : s1.reg r = Glyph.bit b := by simp [hs1, State.tPop, hstk]
  have hs1rP : s1.reg rP = Glyph.bit bt := by simp [hs1, State.tPop, hrP', hrPv]
  have hs1stk0 : s1.stk 0 = L'.map Glyph.bit ++ [Glyph.iend] ++ R := by
    simp [hs1, State.tPop, hstk]
  have hs1stkd : s1.stk dst = s.stk dst := by simp [hs1, State.tPop, h0]
  have hs2rP : s2.reg rP = Glyph.bit bt := by simp [hs2, State.tPush, hs1rP]
  have e1 : Eval main (.pop 0 r) s s1 1 := by
    rw [hs1]; exact Work.Kernel.eval_pop main 0 r s
  have e2 : Eval main (.push dst r) s1 s2 1 := by
    rw [hs2]; exact Work.Kernel.eval_push main dst r s1
  have e3 : Eval main (SG.toggle rP) s2 s3 2 := by
    rw [hs3]; exact toggle_bit main rP bt s2 hs2rP
  have e4 : Eval main (.set rF SG.gGo) s3 s4 1 := by
    rw [hs4]; exact Work.Kernel.eval_set main rF SG.gGo s3
  have hne : s1.reg r ≠ Glyph.iend := by rw [hs1reg]; simp
  refine ⟨s4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [SG.parseBody]
    exact Eval.seq e1 (Eval.iteF hne (Eval.seq e2 (Eval.seq e3 e4)))
  · simp [hs4, hs3, hs2, hs1, State.tPush, State.tPop, h0', h0, hstk]
  · simp [hs4, hs3, hs2, hs1, State.tPush, State.tPop, h0', h0, hstk]
  · simp [hs4, hs3, hPF]
  · simp [hs4]
  · intro k hk0 hkd
    simp [hs4, hs3, hs2, hs1, State.tPush, State.tPop, hk0, hkd]

/-- One iteration of the parse loop when the bits are exhausted: the delimiter `iend` is pushed
back and the loop flag is set to `gStop`. -/
theorem parseBody_iend (main : Cmd) (dst : Stk) (r rP rF : Reg) (h0 : dst ≠ 0)
    (hrP : r ≠ rP) (hPF : rP ≠ rF) (R : List Glyph) (s : State)
    (hstk : s.stk 0 = Glyph.iend :: R) :
    ∃ s₁, Eval main (SG.parseBody dst r rP rF) s s₁ 4 ∧
      s₁.stk 0 = Glyph.iend :: R ∧ s₁.stk dst = s.stk dst ∧
      s₁.reg rP = s.reg rP ∧ s₁.reg rF = SG.gStop ∧
      (∀ k, k ≠ 0 → k ≠ dst → s₁.stk k = s.stk k) := by
  have h0' : (0 : Stk) ≠ dst := fun h => h0 h.symm
  have hrP' : rP ≠ r := fun h => hrP h.symm
  set s1 : State := State.tPop s 0 r with hs1
  set s2 : State := State.tPush s1 0 r with hs2
  set s3 : State := s2.updReg rF SG.gStop with hs3
  have hs1reg : s1.reg r = Glyph.iend := by simp [hs1, State.tPop, hstk]
  have hs1rP : s1.reg rP = s.reg rP := by simp [hs1, State.tPop, hrP']
  have hs1stk0 : s1.stk 0 = R := by simp [hs1, State.tPop, hstk]
  have hs1stkd : s1.stk dst = s.stk dst := by simp [hs1, State.tPop, h0]
  have e1 : Eval main (.pop 0 r) s s1 1 := by
    rw [hs1]; exact Work.Kernel.eval_pop main 0 r s
  have e2 : Eval main (.push 0 r) s1 s2 1 := by
    rw [hs2]; exact Work.Kernel.eval_push main 0 r s1
  have e3 : Eval main (.set rF SG.gStop) s2 s3 1 := by
    rw [hs3]; exact Work.Kernel.eval_set main rF SG.gStop s2
  refine ⟨s3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [SG.parseBody]
    exact Eval.seq e1 (Eval.iteT hs1reg (Eval.seq e2 e3))
  · simp [hs3, hs2, State.tPush, hs1reg, hs1stk0]
  · simp [hs3, hs2, hs1, State.tPush, State.tPop, h0', h0]
  · simp [hs3, hs2, State.tPush, hPF, hs1rP]
  · simp [hs3]
  · intro k hk0 hkd
    simp [hs3, hs2, hs1, State.tPush, State.tPop, hk0]

/-! ## The parse loop -/

/-- The parse loop: after the parse of `L`, stack 0 holds `iend :: R`, the bits are on `dst` in
reverse order, `rP` records the parity and the loop has stopped (`rF = gStop`). -/
theorem parseLoopEval (main : Cmd) (dst : Stk) (r rP rF : Reg) (h0 : dst ≠ 0) (hrP : r ≠ rP)
    (hPF : rP ≠ rF) :
    ∀ (L : List Bool) (bt : Bool) (R : List Glyph) (s : State),
      s.stk 0 = L.map Glyph.bit ++ [Glyph.iend] ++ R →
      s.reg rF = SG.gGo → s.reg rP = Glyph.bit bt →
      ∃ s' n, Eval main (.loop rF SG.gGo (SG.parseBody dst r rP rF)) s s' n ∧
        n ≤ 7 * L.length + 6 ∧
        s'.stk 0 = Glyph.iend :: R ∧
        s'.stk dst = (L.map Glyph.bit).reverse ++ s.stk dst ∧
        s'.reg rP = Glyph.bit (flipB bt L.length) ∧
        s'.reg rF = SG.gStop ∧
        (∀ k, k ≠ 0 → k ≠ dst → s'.stk k = s.stk k) := by
  intro L
  induction L with
  | nil =>
    intro bt R s hstk hrF hrPv
    obtain ⟨s1, hev, hk0, hkd, hregP, hregF, hoth⟩ :=
      parseBody_iend main dst r rP rF h0 hrP hPF R s hstk
    have hne : s1.reg rF ≠ SG.gGo := by rw [hregF]; decide
    have hloop : Eval main (.loop rF SG.gGo (SG.parseBody dst r rP rF)) s s1 6 := by
      have h := Eval.loopT hrF hev (Eval.loopF (main := main) (c := SG.gGo) hne)
      simpa using h
    refine ⟨s1, 6, hloop, ?_, hk0, ?_, ?_, hregF, hoth⟩
    · simp
    · rw [hkd]; simp
    · rw [hregP, hrPv]; simp [flipB]
  | cons b L' ih =>
    intro bt R s hstk hrF hrPv
    obtain ⟨s1, hev, hk0, hkd, hregP, hregF, hoth⟩ :=
      parseBody_bit main dst r rP rF h0 hrP hPF b bt L' R s hstk hrPv
    obtain ⟨s', n', hloop', hn', hk0', hkd', hregP', hregF', hoth'⟩ :=
      ih (!bt) R s1 hk0 hregF hregP
    have hloop : Eval main (.loop rF SG.gGo (SG.parseBody dst r rP rF)) s s' (6 + n' + 1) :=
      Eval.loopT hrF hev hloop'
    refine ⟨s', 6 + n' + 1, hloop, ?_, hk0', ?_, ?_, hregF', ?_⟩
    · simp only [List.length_cons] at hn' ⊢
      omega
    · rw [hkd', hkd]
      simp [List.map_cons, List.reverse_cons]
    · rw [hregP', flipB_not]
      simp only [List.length_cons]
      rw [flipB_succ]
    · intro k hk0 hkd
      rw [hoth' k hk0 hkd, hoth k hk0 hkd]

/-! ## The target statement -/

theorem parseToEval (main : HvdH.Cmd) (dst : HvdH.Stk) (r rP rF : HvdH.Reg)
    (h0 : dst ≠ 0) (hrP : r ≠ rP) (hrF : r ≠ rF) (hPF : rP ≠ rF)
    (L : List Bool) (R : List HvdH.Glyph) (s : HvdH.State)
    (hstk : s.stk 0 = L.map HvdH.Glyph.bit ++ [HvdH.Glyph.iend] ++ R) :
    ∃ s' n, HvdH.Eval main (Work.IntLib.SG.parseTo dst r rP rF) s s' n ∧
      n ≤ 7 * L.length + 10 ∧
      s'.stk 0 = HvdH.Glyph.iend :: R ∧
      s'.stk dst = (L.map HvdH.Glyph.bit).reverse ++ s.stk dst ∧
      s'.reg rP = HvdH.Glyph.bit (decide (L.length % 2 = 1)) ∧
      (∀ k : HvdH.Stk, k ≠ 0 → k ≠ dst → s'.stk k = s.stk k) := by
  set sa : State := s.updReg rP (Glyph.bit false) with hsa
  set sb : State := sa.updReg rF SG.gGo with hsb
  have e1 : Eval main (.set rP (Glyph.bit false)) s sa 1 := by
    rw [hsa]; exact Work.Kernel.eval_set main rP (Glyph.bit false) s
  have e2 : Eval main (.set rF SG.gGo) sa sb 1 := by
    rw [hsb]; exact Work.Kernel.eval_set main rF SG.gGo sa
  have hstkb : sb.stk 0 = L.map Glyph.bit ++ [Glyph.iend] ++ R := by
    rw [hsb, hsa, State.updReg_stk, State.updReg_stk]; exact hstk
  have hrFb : sb.reg rF = SG.gGo := by simp [hsb]
  have hrPb : sb.reg rP = Glyph.bit false := by simp [hsb, hsa, hPF]
  obtain ⟨s', n, hloop, hn, hk0, hkd, hregP, hregF, hoth⟩ :=
    parseLoopEval main dst r rP rF h0 hrP hPF L false R sb hstkb hrFb hrPb
  refine ⟨s', 1 + (1 + n), ?_, ?_, hk0, ?_, ?_, ?_⟩
  · rw [SG.parseTo]
    exact Eval.seq e1 (Eval.seq e2 hloop)
  · omega
  · simp only [hkd, hsb, hsa, State.updReg_stk]
  · rw [hregP, flipB_false]
  · intro k hk0 hkd
    simp only [hoth k hk0 hkd, hsb, hsa, State.updReg_stk]

end Work.IntLib.SqrtGcd
