import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Kernel.roll_mvSeq_ev

set_option autoImplicit false

namespace Work.Kernel

open HvdH

theorem roll_drop_eq_getD_tail (vs : List Val) (k : ℕ) (hk : k < vs.length) :
    vs.drop k = vs.getD k Val.nil :: (vs.drop k).tail := by
  rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem vs Val.nil hk, List.tail_cons]

theorem roll_eraseIdx_eq (vs : List Val) (k : ℕ) :
    vs.eraseIdx k = vs.take k ++ (vs.drop k).tail := by
  rw [List.eraseIdx_eq_take_drop_succ, List.tail_drop]

theorem roll_take_succ_sum (vs : List Val) (k : ℕ) (hk : k < vs.length) :
    ((vs.take (k + 1)).map vsz).sum = ((vs.take k).map vsz).sum + vsz (vs.getD k Val.nil) := by
  rw [List.take_succ_eq_append_getElem hk, List.map_append, List.sum_append,
    List.getD_eq_getElem vs Val.nil hk]
  simp

theorem roll_reverse_sum (us : List Val) :
    (((us.reverse).map vsz).sum) = ((us.map vsz).sum) := by
  rw [List.map_reverse, List.sum_reverse]

theorem roll_length_take (vs : List Val) (k : ℕ) (hk : k < vs.length) :
    (vs.take k).length = k := by
  rw [List.length_take]; omega

/-! ## The `roll` program: state-level statement -/

theorem roll_prog_ev (main : Cmd) (k : ℕ) (vs : List Val) (R : List Glyph) (s : State)
    (hk : k < vs.length) (hR : s.stk 0 = encs vs ++ R) :
    ∃ s' n, Work.Layout.Ev main (roll_prog k) s s' n ∧
      n ≤ 64 * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) ∧
      s'.stk 0 = encs (vs.getD k Val.nil :: vs.eraseIdx k) ++ R ∧
      (∀ j : Stk, j ≠ 0 → s'.stk j = s.stk j) := by
  set v : Val := vs.getD k Val.nil with hv
  set tl : List Val := (vs.drop k).tail with htl
  set Sm : ℕ := ((vs.take (k + 1)).map vsz).sum with hSm
  set S : ℕ := ((vs.take k).map vsz).sum with hS
  have hdrop : vs.drop k = v :: tl := by rw [hv, htl]; exact roll_drop_eq_getD_tail vs k hk
  have herase : vs.eraseIdx k = vs.take k ++ tl := by rw [htl]; exact roll_eraseIdx_eq vs k
  have hSmS : Sm = S + vsz v := by rw [hSm, hS, roll_take_succ_sum vs k hk, hv]
  have hsplit : encs vs = encs (vs.take k) ++ encs (vs.drop k) := by
    rw [← encs_append, List.take_append_drop]
  -- ### phase 1: save the top `k` values on stack `roll_stkA`
  obtain ⟨s1, n1, hev1, hn1, h1a, h1b, h1c, h1d, h1f⟩ :=
    roll_mvSeq_ev (main := main) (a := (0 : Stk)) (b := roll_stkA) (c := roll_stkC)
      (d := roll_stkD) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (vs.take k) (encs (vs.drop k) ++ R) (s.stk roll_stkA) s.reg s.stk
      (by rw [hR, hsplit, List.append_assoc]) rfl
  rw [roll_length_take vs k hk] at hev1
  -- ### phase 2: move the exposed `k`-th value to stack `roll_stkB`
  have h2ha : s1.stk 0 = v.enc ++ (encs tl ++ R) := by
    rw [h1a, hdrop, encs_cons, List.append_assoc]
  obtain ⟨s2, n2, hev2, hn2, h2a, h2b, h2c, h2d, h2f⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := (0 : Stk)) (b := roll_stkB) (c := roll_stkC)
      (d := roll_stkD) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (v := v) (A := encs tl ++ R) (B := s1.stk roll_stkB) (g := s1.reg) (X := s1.stk)
      h2ha rfl
  -- ### phase 3: move the `k` saved values back onto stack 0
  have h3ha : s2.stk roll_stkA = encs (vs.take k).reverse ++ s.stk roll_stkA := by
    rw [h2f roll_stkA (by decide) (by decide) (by decide) (by decide), h1b]
  obtain ⟨s3, n3, hev3, hn3, h3a, h3b, h3c, h3d, h3f⟩ :=
    roll_mvSeq_ev (main := main) (a := roll_stkA) (b := (0 : Stk)) (c := roll_stkC)
      (d := roll_stkD) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ((vs.take k).reverse) (s.stk roll_stkA) (s2.stk 0) (s2.reg) (s2.stk) h3ha rfl
  rw [List.length_reverse, roll_length_take vs k hk] at hev3
  have h3b' : s3.stk 0 = encs (vs.take k) ++ (encs tl ++ R) := by
    rw [h3b, h2a, List.reverse_reverse]
  -- ### phase 4: put the saved `k`-th value back on top
  have h4ha : s3.stk roll_stkB = v.enc ++ s.stk roll_stkB := by
    rw [h3f roll_stkB (by decide) (by decide) (by decide) (by decide), h2b,
      h1f roll_stkB (by decide) (by decide) (by decide) (by decide)]
  obtain ⟨s4, n4, hev4, hn4, h4a, h4b, h4c, h4d, h4f⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := roll_stkB) (b := (0 : Stk)) (c := roll_stkC)
      (d := roll_stkD) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (v := v) (A := s.stk roll_stkB) (B := s3.stk 0) (g := s3.reg) (X := s3.stk) h4ha rfl
  have hfin : s4.stk 0 = encs (v :: vs.eraseIdx k) ++ R := by
    rw [h4b, h3b', herase, encs_cons, encs_append]
    simp only [List.append_assoc]
  have hframe : ∀ j : Stk, j ≠ 0 → s4.stk j = s.stk j := by
    intro j hj0
    by_cases hjA : j = roll_stkA
    · subst hjA
      rw [h4f roll_stkA (by decide) (by decide) (by decide) (by decide), h3a]
    by_cases hjB : j = roll_stkB
    · subst hjB
      exact h4a
    by_cases hjC : j = roll_stkC
    · subst hjC
      rw [h4c, h3c, h2c, h1c]
    by_cases hjD : j = roll_stkD
    · subst hjD
      rw [h4d, h3d, h2d, h1d]
    · rw [h4f j hjB hj0 hjC hjD, h3f j hjA hj0 hjC hjD, h2f j hj0 hjB hjC hjD,
        h1f j hj0 hjA hjC hjD]
  have hev : Work.Layout.Ev main (roll_prog k) s s4 (n1 + n2 + n3 + n4) := by
    have h := Work.Layout.Ev.seq hev1
      (Work.Layout.Ev.seq hev2 (Work.Layout.Ev.seq hev3 hev4))
    exact h.mono (by omega)
  -- ### cost
  have hn1' : n1 ≤ 16 * (S + k + 1) := by
    have h := hn1; rw [roll_length_take vs k hk, ← hS] at h; exact h
  have hn3' : n3 ≤ 16 * (S + k + 1) := by
    have h := hn3
    rw [List.length_reverse, roll_length_take vs k hk, roll_reverse_sum (vs.take k), ← hS] at h
    exact h
  have hcost : n1 + n2 + n3 + n4 ≤ 64 * (k + 1) * (Sm + 1) := by
    have h1 : 32 * (Sm + k + 2) ≤ 64 * (k + 1) * (Sm + 1) := by
      have hk1 : Sm + 1 ≤ (k + 1) * (Sm + 1) := by
        simpa using Nat.mul_le_mul (by omega : 1 ≤ k + 1) (le_refl (Sm + 1))
      have hk2 : k + 1 ≤ (k + 1) * (Sm + 1) := by
        simpa using Nat.mul_le_mul (le_refl (k + 1)) (by omega : 1 ≤ Sm + 1)
      calc 32 * (Sm + k + 2) = 32 * (Sm + 1) + 32 * (k + 1) := by ring
        _ ≤ 32 * ((k + 1) * (Sm + 1)) + 32 * ((k + 1) * (Sm + 1)) :=
              Nat.add_le_add (Nat.mul_le_mul_left 32 hk1) (Nat.mul_le_mul_left 32 hk2)
        _ = 64 * (k + 1) * (Sm + 1) := by ring
    have h2 : n1 + n2 + n3 + n4 ≤ 32 * (Sm + k + 2) := by
      rw [hSmS]; omega
    exact le_trans h2 h1
  exact ⟨s4, n1 + n2 + n3 + n4, hev, hcost, hfin, hframe⟩

/-! ## `Work.Kernel.roll` -/

/-- `roll` field of `HvdH.KernelLib` (v2/v3).  Imports: `Submission.Work.Kernel.Raw`, `Submission.Work.Kernel.Pend`, and the already-proved marker movers `Submission.Work.Layout.Move` (`Work.Layout.Ev` = bounded `Eval`; `mvVal_ev` moves one value between two stacks in normal order at cost `≤ 16*(vsz v+1)`, touching only its four stack arguments) — using them saves hours.  Plan: move the top `k` values of stack 0 one by one to one scratch stack (marker before each value, shared bottom marker first, using the pending counter as in `Submission/Work/Kernel/dropValue*.lean`); then move the exposed `k`-th value to a second scratch stack; then move the `k` saved values back onto stack 0 (each move-back pops down to one marker), and finally move the saved `k`-th value back on top.  Each value is moved O(1) times, giving `K*(k+1)*(Σ_{i≤k} vsz + 1)`.  Helpers must be named with the prefix `roll_`. -/
theorem roll : ∃ (prog : ℕ → HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (k : ℕ), HvdH.WordR main (prog k)
    (fun vs => k < vs.length) (fun vs out => out = vs.getD k HvdH.Val.nil :: vs.eraseIdx k)
    (fun vs => K * (k + 1) * (((vs.take (k + 1)).map HvdH.vsz).sum + 1)) := by
  refine ⟨roll_prog, 64, ?_⟩
  intro main k vs hk s R hR
  obtain ⟨s', n, hev, hcost, h0, hframe⟩ := roll_prog_ev main k vs R s hk hR
  obtain ⟨n0, heval, hn0⟩ := hev
  exact ⟨vs.getD k Val.nil :: vs.eraseIdx k, s', n0, rfl, heval, le_trans hn0 hcost, h0, hframe⟩

end Work.Kernel
