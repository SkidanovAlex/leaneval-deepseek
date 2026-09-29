import Mathlib
import Submission.Work.IntLib.parseEmitDefs
import Submission.Work.IntLib.Raw

set_option autoImplicit false

namespace Work.IntLib

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-- Loop-level core of `drainAllEval`: from a state whose stack `k` holds exactly `gs` (with no
`eos` among them), whose register `r` holds `eos` and whose stack `k'` holds `bk`, the loop
`drainLoop k k' r` empties stack `k`, moves its content reversed on top of `bk`, and stops with
`reg r = mk 15`; the cost is at most `5 * gs.length + 5`. -/
theorem drainLoop_eval_aux (main : Cmd) (k k' : Stk) (hkk : k ≠ k') (r : Reg) (gs bk : List Glyph)
    (s : State) (hne : ∀ g ∈ gs, g ≠ Glyph.eos) (hstk : s.stk k = gs)
    (hreg : s.reg r = Glyph.eos) (hk' : s.stk k' = bk) :
    ∃ s' n, Eval main (drainLoop k k' r) s s' n ∧ n ≤ 5 * gs.length + 5 ∧
      s'.stk k = [] ∧ s'.stk k' = gs.reverse ++ bk ∧ s'.reg r = Glyph.mk 15 ∧
      (∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) := by
  induction gs generalizing bk s with
  | nil =>
    -- the terminating iteration: `pop` on an empty stack leaves the state unchanged
    have hsreg : Function.update s.reg r ((s.stk k).headD Glyph.eos) = s.reg := by
      rw [hstk, List.headD_nil]
      simpa [hreg] using Function.update_eq_self r s.reg
    have hsstk : Function.update s.stk k (s.stk k).tail = s.stk := by
      rw [hstk, List.tail_nil]
      simpa [hstk] using Function.update_eq_self k s.stk
    have hstate : (⟨Function.update s.reg r ((s.stk k).headD Glyph.eos),
        Function.update s.stk k (s.stk k).tail⟩ : State) = s := State.ext_mk (s := s) hsreg hsstk
    have hpop : Eval main (.pop k r) s s 1 := by
      have h := HvdH.Eval.pop (main := main) k r s
      rw [hstate] at h
      exact h
    let F : State := s.updReg r (Glyph.mk 15)
    have hset : Eval main (.set r (Glyph.mk 15)) s F 1 :=
      Eval.set_eq (main := main) (r := r) (c := Glyph.mk 15) (s := s)
    have hite : Eval main (.ite r Glyph.eos (.set r (Glyph.mk 15))
        (.push k' r ;;; .set r Glyph.eos)) s F 2 := Eval.iteT hreg hset
    have hbody : Eval main (drainBody k k' r) s F 3 := by
      have h := Eval.seq hpop hite
      simpa [drainBody] using h
    have hstop : F.reg r ≠ Glyph.eos := by simp [F]
    have hloopF : Eval main (drainLoop k k' r) F F 1 := Eval.loopF (main := main) hstop
    have hloop : Eval main (drainLoop k k' r) s F 5 :=
      Eval.loopT (n := 3) (m := 1) hreg hbody hloopF
    refine ⟨F, 5, hloop, by simp, ?_, ?_, ?_, ?_⟩
    · simp [F, hstk]
    · simp [F, hk']
    · simp [F]
    · intro j _ _
      simp [F]
  | cons g gs ih =>
    have hg : g ≠ Glyph.eos := hne g (List.mem_cons_self ..)
    have hne' : ∀ x ∈ gs, x ≠ Glyph.eos := fun x hx => hne x (List.mem_cons_of_mem g hx)
    -- one moving iteration of the loop
    let A : State := (s.updStk k gs).updReg r g
    have hpop : Eval main (.pop k r) s A 1 := Eval.pop_cons (main := main) (k := k) (r := r) hstk
    have hAr : A.reg r = g := by simp [A]
    let B : State := A.updStk k' (A.reg r :: A.stk k')
    have hpush : Eval main (.push k' r) A B 1 :=
      Eval.push_eq (main := main) (k := k') (r := r) (g := A.reg r) rfl
    let C : State := B.updReg r Glyph.eos
    have hset : Eval main (.set r Glyph.eos) B C 1 := Eval.set_eq
    have hneA : A.reg r ≠ Glyph.eos := by rw [hAr]; exact hg
    have hite : Eval main (.ite r Glyph.eos (.set r (Glyph.mk 15))
        (.push k' r ;;; .set r Glyph.eos)) A C 3 :=
      Eval.iteF (c := Glyph.eos) hneA (Eval.seq hpush hset)
    have hbody : Eval main (drainBody k k' r) s C 4 := by
      have h := Eval.seq hpop hite
      simpa [drainBody] using h
    -- invariants after that iteration
    have hAk : A.stk k = gs := by simp [A]
    have hAk' : A.stk k' = bk := by simp [A, hk', Ne.symm hkk]
    have hCk : C.stk k = gs := by
      have h2 : C.stk k = A.stk k := by simp [C, B, hkk]
      rw [h2, hAk]
    have hCk' : C.stk k' = g :: bk := by
      have h2 : C.stk k' = A.reg r :: A.stk k' := by simp [C, B]
      rw [h2, hAr, hAk']
    have hCr : C.reg r = Glyph.eos := by simp [C, B, A]
    have hCoth : ∀ j : Stk, j ≠ k → j ≠ k' → C.stk j = s.stk j := by
      intro j hj1 hj2
      have h2 : C.stk j = B.stk j := by simp [C]
      have h3 : B.stk j = A.stk j := by simp [B, hj2]
      have h4 : A.stk j = s.stk j := by simp [A, hj1]
      rw [h2, h3, h4]
    obtain ⟨s', n, hev, hn, hsk, hsk', hsr, hoth⟩ := ih (g :: bk) C hne' hCk hCr hCk'
    have hloop : Eval main (drainLoop k k' r) s s' (4 + n + 1) := Eval.loopT hreg hbody hev
    refine ⟨s', 4 + n + 1, hloop, ?_, hsk, ?_, hsr, ?_⟩
    · simp only [List.length_cons]; omega
    · calc s'.stk k' = gs.reverse ++ (g :: bk) := hsk'
        _ = (g :: gs).reverse ++ bk := by simp [List.reverse_cons, List.append_assoc]
    · intro j hj1 hj2
      rw [hoth j hj1 hj2, hCoth j hj1 hj2]

theorem drainAllEval (main : HvdH.Cmd) (k k' : HvdH.Stk) (hkk : k ≠ k') (r : HvdH.Reg)
    (gs : List HvdH.Glyph) (s : HvdH.State) (hne : ∀ g ∈ gs, g ≠ HvdH.Glyph.eos) (hstk : s.stk k = gs) :
    ∃ (s' : HvdH.State) (n : ℕ), n ≤ 5 * gs.length + 6 ∧
      HvdH.Eval main (Work.IntLib.drainAll k k' r) s s' n ∧
      s'.stk k = [] ∧ s'.stk k' = gs.reverse ++ s.stk k' ∧ s'.reg r = HvdH.Glyph.mk 15 ∧
      (∀ j : HvdH.Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) := by
  let s₁ : State := s.updReg r Glyph.eos
  have hs₁k : s₁.stk k = gs := by simp [s₁, hstk]
  have hs₁r : s₁.reg r = Glyph.eos := by simp [s₁]
  obtain ⟨s', n, hev, hn, hsk, hsk', hsr, hoth⟩ :=
    drainLoop_eval_aux main k k' hkk r gs (s.stk k') s₁ hne hs₁k hs₁r rfl
  refine ⟨s', 1 + n, by omega, ?_, hsk, hsk', hsr, ?_⟩
  · have hset : Eval main (.set r Glyph.eos) s s₁ 1 := Eval.set_eq
    have h := Eval.seq hset hev
    simpa [drainAll] using h
  · intro j hj1 hj2
    exact hoth j hj1 hj2

end Work.IntLib
