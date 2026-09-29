import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auRoundAux
import Submission.Work.Resample.auParkDefs
import Submission.Work.Resample.auParkSteps

/-!
# `Work.Resample.auCWPark`

The program re-arranges the top fifteen values of stack `0`

  `[rec, li, zi, lr, zr, M, sh, k, x, y, W, Pv, Lor, Loi, CHAIN]`

into

  `[Pv, lr, li, cons rec CHAIN]`

without ever reading `CHAIN`: the four surviving values are parked on stack `1` (in the order
`rec, li, lr, Pv`, so that popping the parking stack returns them in exactly the order in which
they must be re-pushed), the ten unwanted values are deleted, and the output is rebuilt on top of
the still untouched `CHAIN.enc`.

Step sequence (all costs `<= KB * (S + 1)`, `22` steps in total):

1.  `roll 11`: bring `Pv` to the top;           2.  park `Pv`;
3.  `roll 3`:  bring `lr` to the top;           4.  park `lr`;
5.  `roll 1`:  bring `li` to the top;           6.  park `li`;
7.  park `rec`;
8-17. drop `zi, zr, M, sh, k, x, y, W, Lor, Loi`;
18. restore `rec` on top of `CHAIN`;            19. `consV`: form `cons rec CHAIN`;
20. restore `li`;                               21. restore `lr`;   22. restore `Pv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.Resample

open HvdH

theorem auCWPark (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd)
      (rec li zi lr zr M sh k x y W Pv Lor Loi CHAIN : HvdH.Val) (S : ℕ),
      (∀ v ∈ [rec, li, zi, lr, zr, M, sh, k, x, y, W, Pv, Lor, Loi], HvdH.vsz v ≤ S) →
      Work.Resample.Pipe main prog
        [rec, li, zi, lr, zr, M, sh, k, x, y, W, Pv, Lor, Loi, CHAIN]
        [Pv, lr, li, HvdH.Val.cons rec CHAIN]
        (K * (S + 1)) := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨dropP, Kd, hdrop⟩ := hk.drop
  obtain ⟨consP, Kc, hcons⟩ := hk.consV
  obtain ⟨pushP, Kp, hpush⟩ := auRoundPush 1 (by decide)
  obtain ⟨popP, Kq, hpop⟩ := auRoundPop 1 (by decide)
  -- uniform per-step budget
  let KB : ℕ := Kr * 441 + Kp + Kq + Kd + Kc + 1
  have hKB : KB = Kr * 441 + Kp + Kq + Kd + Kc + 1 := rfl
  have hKr : Kr * 21 * 21 ≤ KB := by rw [hKB]; omega
  have hKp : Kp ≤ KB := by rw [hKB]; omega
  have hKq : Kq ≤ KB := by rw [hKB]; omega
  have hKd : Kd ≤ KB := by rw [hKB]; omega
  have hKc : Kc ≤ KB := by rw [hKB]; omega
  -- the program: `roll · push · roll · push · roll · push · push · (drop)¹⁰ ·
  -- pop · consV · pop · pop · pop`
  let prog : Cmd := Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq ((rollP 11)) pushP) (rollP 3)) pushP) (rollP 1)) pushP) pushP) dropP) dropP) dropP) dropP) dropP) dropP) dropP) dropP) dropP) dropP) popP) consP) popP) popP) popP
  refine ⟨prog, 22 * KB, ?_⟩
  intro main rec li zi lr zr M sh k x y W Pv Lor Loi CHAIN S hS
  refine Pipe.ofPark (fun rest => ?_)
  -- the successive value-stack windows (and the contents of the parking stack `1`)
  let A0 : List Val := [rec, li, zi, lr, zr, M, sh, k, x, y, W, Pv, Lor, Loi, CHAIN]
  let A1 : List Val := [Pv, rec, li, zi, lr, zr, M, sh, k, x, y, W, Lor, Loi, CHAIN]
  let A2 : List Val := [rec, li, zi, lr, zr, M, sh, k, x, y, W, Lor, Loi, CHAIN]
  let A3 : List Val := [lr, rec, li, zi, zr, M, sh, k, x, y, W, Lor, Loi, CHAIN]
  let A4 : List Val := [rec, li, zi, zr, M, sh, k, x, y, W, Lor, Loi, CHAIN]
  let A5 : List Val := [li, rec, zi, zr, M, sh, k, x, y, W, Lor, Loi, CHAIN]
  let A6 : List Val := [rec, zi, zr, M, sh, k, x, y, W, Lor, Loi, CHAIN]
  let A7 : List Val := [zi, zr, M, sh, k, x, y, W, Lor, Loi, CHAIN]
  let A8 : List Val := [zr, M, sh, k, x, y, W, Lor, Loi, CHAIN]
  let A9 : List Val := [M, sh, k, x, y, W, Lor, Loi, CHAIN]
  let A10 : List Val := [sh, k, x, y, W, Lor, Loi, CHAIN]
  let A11 : List Val := [k, x, y, W, Lor, Loi, CHAIN]
  let A12 : List Val := [x, y, W, Lor, Loi, CHAIN]
  let A13 : List Val := [y, W, Lor, Loi, CHAIN]
  let A14 : List Val := [W, Lor, Loi, CHAIN]
  let A15 : List Val := [Lor, Loi, CHAIN]
  let A16 : List Val := [Loi, CHAIN]
  let A17 : List Val := [CHAIN]
  let A18 : List Val := [rec, CHAIN]
  let A19 : List Val := [Val.cons rec CHAIN]
  let A20 : List Val := [li, Val.cons rec CHAIN]
  let A21 : List Val := [lr, li, Val.cons rec CHAIN]
  let A22 : List Val := [Pv, lr, li, Val.cons rec CHAIN]
  let P1 : List Val := [Pv]
  let P2 : List Val := [lr, Pv]
  let P3 : List Val := [li, lr, Pv]
  let P4 : List Val := [rec, li, lr, Pv]
  let P5 : List Val := [li, lr, Pv]
  let P6 : List Val := [lr, Pv]
  let P7 : List Val := [Pv]
  -- the scan: bring the four survivors to the top in turn and park them
  have s1 : WordM main (rollP 11) (PreD (A0 ++ rest) []) (PostD (A1 ++ rest) [])
      (fun _ _ => KB * (S + 1)) :=
    auParkStepRoll (h := hroll) (hK := hKr) (V := A0 ++ rest) (j := 11)
      (hj := by
        have h : (A0 ++ rest).length = 15 + rest.length := by
          simp only [A0, List.length_append, List.length_cons, List.length_nil]
        omega)
      (h21 := by omega)
      (hv := by
        intro z hz
        apply hS
        have ht : (A0 ++ rest).take 12 = [rec, li, zi, lr, zr, M, sh, k, x, y, W, Pv] := by
          simp only [A0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
        rw [ht] at hz
        simp only [List.mem_cons, List.mem_nil_iff] at hz ⊢
        tauto)
  have s2 : WordM main pushP (PreD (A1 ++ rest) []) (PostD (A2 ++ rest) P1)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepPush (h := hpush) (hK := hKp) (hv := hS Pv (by simp)) (v := Pv)
  have s3 : WordM main (rollP 3) (PreD (A2 ++ rest) P1) (PostD (A3 ++ rest) P1)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepRoll (h := hroll) (hK := hKr) (V := A2 ++ rest) (j := 3)
      (hj := by
        have h : (A2 ++ rest).length = 14 + rest.length := by
          simp only [A2, List.length_append, List.length_cons, List.length_nil]
        omega)
      (h21 := by omega)
      (hv := by
        intro z hz
        apply hS
        have ht : (A2 ++ rest).take 4 = [rec, li, zi, lr] := by
          simp only [A2, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
        rw [ht] at hz
        simp only [List.mem_cons, List.mem_nil_iff] at hz ⊢
        tauto)
  have s4 : WordM main pushP (PreD (A3 ++ rest) P1) (PostD (A4 ++ rest) P2)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepPush (h := hpush) (hK := hKp) (hv := hS lr (by simp)) (v := lr)
  have s5 : WordM main (rollP 1) (PreD (A4 ++ rest) P2) (PostD (A5 ++ rest) P2)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepRoll (h := hroll) (hK := hKr) (V := A4 ++ rest) (j := 1)
      (hj := by
        have h : (A4 ++ rest).length = 13 + rest.length := by
          simp only [A4, List.length_append, List.length_cons, List.length_nil]
        omega)
      (h21 := by omega)
      (hv := by
        intro z hz
        apply hS
        have ht : (A4 ++ rest).take 2 = [rec, li] := by
          simp only [A4, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
        rw [ht] at hz
        simp only [List.mem_cons, List.mem_nil_iff] at hz ⊢
        tauto)
  have s6 : WordM main pushP (PreD (A5 ++ rest) P2) (PostD (A6 ++ rest) P3)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepPush (h := hpush) (hK := hKp) (hv := hS li (by simp)) (v := li)
  have s7 : WordM main pushP (PreD (A6 ++ rest) P3) (PostD (A7 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepPush (h := hpush) (hK := hKp) (hv := hS rec (by simp)) (v := rec)
  -- delete the ten unwanted values (this leaves `[CHAIN]` above the untouched `CHAIN.enc`)
  have s8 : WordM main dropP (PreD (A7 ++ rest) P4) (PostD (A8 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS zi (by simp)) (v := zi)
  have s9 : WordM main dropP (PreD (A8 ++ rest) P4) (PostD (A9 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS zr (by simp)) (v := zr)
  have s10 : WordM main dropP (PreD (A9 ++ rest) P4) (PostD (A10 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS M (by simp)) (v := M)
  have s11 : WordM main dropP (PreD (A10 ++ rest) P4) (PostD (A11 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS sh (by simp)) (v := sh)
  have s12 : WordM main dropP (PreD (A11 ++ rest) P4) (PostD (A12 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS k (by simp)) (v := k)
  have s13 : WordM main dropP (PreD (A12 ++ rest) P4) (PostD (A13 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS x (by simp)) (v := x)
  have s14 : WordM main dropP (PreD (A13 ++ rest) P4) (PostD (A14 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS y (by simp)) (v := y)
  have s15 : WordM main dropP (PreD (A14 ++ rest) P4) (PostD (A15 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS W (by simp)) (v := W)
  have s16 : WordM main dropP (PreD (A15 ++ rest) P4) (PostD (A16 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS Lor (by simp)) (v := Lor)
  have s17 : WordM main dropP (PreD (A16 ++ rest) P4) (PostD (A17 ++ rest) P4)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepDrop (h := hdrop) (hK := hKd) (hv := hS Loi (by simp)) (v := Loi)
  -- rebuild the output on top of `CHAIN`
  have s18 : WordM main popP (PreD (A17 ++ rest) P4) (PostD (A18 ++ rest) P5)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepPop (h := hpop) (hK := hKq) (hv := hS rec (by simp)) (v := rec)
  have s19 : WordM main consP (PreD (A18 ++ rest) P5) (PostD (A19 ++ rest) P5)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepCons (h := hcons) (hK := hKc) (a := rec) (b := CHAIN) (V' := rest) (L1 := P5)
  have s20 : WordM main popP (PreD (A19 ++ rest) P5) (PostD (A20 ++ rest) P6)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepPop (h := hpop) (hK := hKq) (hv := hS li (by simp)) (v := li)
  have s21 : WordM main popP (PreD (A20 ++ rest) P6) (PostD (A21 ++ rest) P7)
      (fun _ _ => KB * (S + 1)) :=
    auParkStepPop (h := hpop) (hK := hKq) (hv := hS lr (by simp)) (v := lr)
  have s22 : WordM main popP (PreD (A21 ++ rest) P7) (PostD (A22 ++ rest) [])
      (fun _ _ => KB * (S + 1)) :=
    auParkStepPop (h := hpop) (hK := hKq) (hv := hS Pv (by simp)) (v := Pv)
  -- compose the 22 steps
  have c1 : WordM main (rollP 11) (PreD (A0 ++ rest) []) (PostD (A1 ++ rest) []) (fun _ _ => KB * (S + 1)) := s1
  have c2 := seqSc c1 s2
  have c3 := seqSc c2 s3
  have c4 := seqSc c3 s4
  have c5 := seqSc c4 s5
  have c6 := seqSc c5 s6
  have c7 := seqSc c6 s7
  have c8 := seqSc c7 s8
  have c9 := seqSc c8 s9
  have c10 := seqSc c9 s10
  have c11 := seqSc c10 s11
  have c12 := seqSc c11 s12
  have c13 := seqSc c12 s13
  have c14 := seqSc c13 s14
  have c15 := seqSc c14 s15
  have c16 := seqSc c15 s16
  have c17 := seqSc c16 s17
  have c18 := seqSc c17 s18
  have c19 := seqSc c18 s19
  have c20 := seqSc c19 s20
  have c21 := seqSc c20 s21
  have c22 := seqSc c21 s22
  exact WordM.mono c22 (fun _ _ => Nat.mul_le_mul_right _ (by omega))

end Work.Resample
