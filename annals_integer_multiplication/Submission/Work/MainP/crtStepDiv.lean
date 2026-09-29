import Mathlib
import Submission.Work.MainP.labArith
import Submission.Work.MainP.labStepAux
import Submission.Work.MainP.labStepSave
import Submission.Work.MainP.labStepRestore
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.Base
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false

namespace Work.MainP

open HvdH

local infixl:68 " ;;" => HvdH.Cmd.seq

/-- The `crtStepDiv` program: `q = P / t` is computed, one copy of `int q` is parked on stack 1
(moving the values with `Work.Layout.mvVal`, which restores its scratch stacks), the triple
`triple 0 q P` is consed onto `ofList ACC`, and the parked copy is moved back on top. -/
def crtStepProg (pickP : ℕ → Cmd) (tdP dupP consVP : Cmd) (pushP : Val → Cmd) : Cmd :=
  pickP 1 ;; tdP ;; dupP ;; Work.Layout.mvVal 0 1 14 15 ;; consVP ;; pushP (.int 0) ;;
    consVP ;; consVP ;; Work.Layout.mvVal 1 0 14 15

/-- The per-round step word of the CRT place-value walk: from `int t :: int P :: ofList ACC :: acc`
(with `1 ≤ t`) it produces `int (P / t) :: ofList (triple 0 (P / t) P :: ACC) :: acc`, at cost
`O ((t.size + 1) * (P.size + 1) + (P.size + 2))`.

NOTE (why this exists although `Work.MainP.labStep` already proves the same specification):
`Submission/Work/MainP/labStep.lean` defines `Work.MainP.labProg`, and
`Submission/Work/MainP/labFoldDefs.lean` ALSO defines `Work.MainP.labProg`; therefore NO module can
import both `Submission.Work.MainP.labStep` and `Submission.Work.MainP.labFold`. A client needs both
the fold (`Submission.Work.MainP.labFold`) and this step in a single file, so this must be a
self-contained proof in a module that does NOT import `Submission.Work.MainP.labStep`. Do not import
it; write your own program (give it a fresh name, e.g. `crtStepProg`) and compose the pieces
`labStepAux` / `labStepSave` / `labStepRestore` the same way `labStep.lean` does. -/
theorem crtStepDiv (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (step : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (t P : ℕ), 1 ≤ t →
      ∀ (ACC acc : List HvdH.Val),
      HvdH.WordR main step
        (fun vs => vs = HvdH.Val.int (t : ℤ) :: HvdH.Val.int (P : ℤ) ::
          HvdH.ofList ACC :: acc)
        (fun _ out => out = HvdH.Val.int ((P / t : ℕ) : ℤ) ::
          HvdH.ofList (Work.MainP.triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ACC) :: acc)
        (fun _ => K * ((t.size + 1) * (P.size + 1) + (P.size + 2))) := by
  obtain ⟨pickP, Kp, hpick⟩ := hK.pick
  obtain ⟨tdP, Kd, htd⟩ := hI.tdiv
  obtain ⟨dupP, Kud, hdup⟩ := hK.dup
  obtain ⟨consVP, Kcv, hconsV⟩ := hK.consV
  obtain ⟨pushP, Kpv, hpush⟩ := hK.pushVal
  refine ⟨crtStepProg pickP tdP dupP consVP pushP, 128 * (Kp + Kd + Kud + Kcv + Kpv + 1), ?_⟩
  intro main t P ht ACC acc
  apply WordR_of_WordR1 (P := fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) ::
      ofList ACC :: acc)
    (Q := fun _ out => out = Val.int ((P / t : ℕ) : ℤ) ::
      ofList (triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ACC) :: acc)
    (C := fun _ => 128 * (Kp + Kd + Kud + Kcv + Kpv + 1) *
      ((t.size + 1) * (P.size + 1) + (P.size + 2)))
  intro S1
  -- stage 1: copy `int P` to the top
  have h1 : WordR1 main (pickP 1) S1 S1
      (fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.int (P : ℤ) :: Val.int (t : ℤ) :: Val.int (P : ℤ) ::
        ofList ACC :: acc)
      (fun _ => Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1))) := by
    refine WordR1_of_WordR rfl ?_
    refine wrd_at (hpick main 1) (A := Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (B := Val.int (P : ℤ) :: Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (c := Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1))) ?_ ?_ ?_
    · simp
    · intro out hout
      rw [hout]
      rfl
    · simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Work.Main.vsz_int, Nat.add_zero]
      exact le_of_eq (by ring)
  -- stage 2: `P / t`
  have h2 : WordR1 main tdP S1 S1
      (fun vs => vs = Val.int (P : ℤ) :: Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.int (((P / t : ℕ) : ℤ)) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ => Kd * isz (P : ℤ) * isz (t : ℤ)) := by
    refine WordR1_of_WordR rfl ?_
    refine wrd_at (htd main)
      (A := Val.int (P : ℤ) :: Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (B := Val.int (((P / t : ℕ) : ℤ)) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (c := Kd * isz (P : ℤ) * isz (t : ℤ)) ?_ ?_ ?_
    · refine ⟨(P : ℤ), (t : ℤ), Val.int (P : ℤ) :: ofList ACC :: acc, rfl, ?_⟩
      change (t : ℤ) ≠ 0
      exact_mod_cast (by omega : t ≠ 0)
    · rintro out ⟨a, b, rest, ha, hout⟩
      simp only [List.cons.injEq, Val.int.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      rw [hout, Int.ofNat_tdiv]
    · exact le_refl _
  -- stage 3: duplicate `int q`
  have h3 : WordR1 main dupP S1 S1
      (fun vs => vs = Val.int (((P / t : ℕ) : ℤ)) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.int (((P / t : ℕ) : ℤ)) :: Val.int (((P / t : ℕ) : ℤ)) ::
        Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ => Kud * (isz (((P / t : ℕ) : ℤ)) + 1)) := by
    refine WordR1_of_WordR rfl ?_
    refine wrd_at (hdup main)
      (A := Val.int (((P / t : ℕ) : ℤ)) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (B := Val.int (((P / t : ℕ) : ℤ)) :: Val.int (((P / t : ℕ) : ℤ)) ::
        Val.int (P : ℤ) :: ofList ACC :: acc)
      (c := Kud * (isz (((P / t : ℕ) : ℤ)) + 1)) ?_ ?_ ?_
    · simp
    · rintro out ⟨v, rest, hv, hout⟩
      simp only [List.cons.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      rw [hout]
    · show Kud * (vsz (Val.int (((P / t : ℕ) : ℤ))) + 1) ≤
        Kud * (isz (((P / t : ℕ) : ℤ)) + 1)
      rw [Work.Main.vsz_int]
  -- stage 4: park a copy of `int q` on stack 1
  have h4 : WordR1 main (Work.Layout.mvVal 0 1 14 15) S1
      ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = Val.int (((P / t : ℕ) : ℤ)) :: Val.int (((P / t : ℕ) : ℤ)) ::
        Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.int (((P / t : ℕ) : ℤ)) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ => 16 * (isz (((P / t : ℕ) : ℤ)) + 1)) :=
    labStepSave main S1 (Val.int (P : ℤ) :: ofList ACC :: acc) (((P / t : ℕ) : ℤ))
  -- stage 5: `cons (int q) (int P)`
  have h5 : WordR1 main consVP ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = Val.int (((P / t : ℕ) : ℤ)) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.cons (Val.int (((P / t : ℕ) : ℤ))) (Val.int (P : ℤ)) ::
        ofList ACC :: acc)
      (fun _ => Kcv) := by
    refine WordR1_of_WordR rfl ?_
    refine wrd_at (hconsV main)
      (A := Val.int (((P / t : ℕ) : ℤ)) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (B := Val.cons (Val.int (((P / t : ℕ) : ℤ))) (Val.int (P : ℤ)) :: ofList ACC :: acc)
      (c := Kcv) ?_ ?_ ?_
    · simp
    · rintro out ⟨a, b, rest, ha, hout⟩
      simp only [List.cons.injEq, Val.int.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      rw [hout]
    · exact le_refl _
  -- stage 6: push the constant `int 0`
  have h6 : WordR1 main (pushP (.int 0)) ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = Val.cons (Val.int (((P / t : ℕ) : ℤ))) (Val.int (P : ℤ)) ::
        ofList ACC :: acc)
      (fun _ out => out = Val.int 0 :: Val.cons (Val.int (((P / t : ℕ) : ℤ)))
        (Val.int (P : ℤ)) :: ofList ACC :: acc)
      (fun _ => 3 * Kpv) := by
    refine WordR1_of_WordR rfl ?_
    refine wrd_at (hpush main (.int 0))
      (A := Val.cons (Val.int (((P / t : ℕ) : ℤ))) (Val.int (P : ℤ)) :: ofList ACC :: acc)
      (B := Val.int 0 :: Val.cons (Val.int (((P / t : ℕ) : ℤ))) (Val.int (P : ℤ)) ::
        ofList ACC :: acc)
      (c := 3 * Kpv) trivial ?_ ?_
    · intro out hout
      rw [hout]
    · show Kpv * (vsz (Val.int (0 : ℤ)) + 1) ≤ 3 * Kpv
      rw [Work.Main.vsz_int]
      have hz : isz ((0 : ℤ)) = 2 := by simp [HvdH.isz]
      rw [hz]
      exact le_of_eq (by ring)
  -- stage 7: `triple 0 q P`
  have h7 : WordR1 main consVP ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = Val.int 0 :: Val.cons (Val.int (((P / t : ℕ) : ℤ))) (Val.int (P : ℤ)) ::
        ofList ACC :: acc)
      (fun _ out => out = triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ofList ACC :: acc)
      (fun _ => Kcv) := by
    refine WordR1_of_WordR rfl ?_
    refine wrd_at (hconsV main)
      (A := Val.int 0 :: Val.cons (Val.int (((P / t : ℕ) : ℤ))) (Val.int (P : ℤ)) ::
        ofList ACC :: acc)
      (B := triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ofList ACC :: acc)
      (c := Kcv) ?_ ?_ ?_
    · simp
    · rintro out ⟨a, b, rest, ha, hout⟩
      simp only [List.cons.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      rw [hout]
      rfl
    · exact le_refl _
  -- stage 8: cons the triple onto `ofList ACC`
  have h8 : WordR1 main consVP ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = ofList (triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ACC) :: acc)
      (fun _ => Kcv) := by
    refine WordR1_of_WordR rfl ?_
    refine wrd_at (hconsV main)
      (A := triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ofList ACC :: acc)
      (B := ofList (triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ACC) :: acc)
      (c := Kcv) ?_ ?_ ?_
    · simp
    · rintro out ⟨a, b, rest, ha, hout⟩
      simp only [List.cons.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      rw [hout]
      rfl
    · exact le_refl _
  -- stage 9: bring the parked copy of `int q` back on top
  have h9 : WordR1 main (Work.Layout.mvVal 1 0 14 15)
      ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1) S1
      (fun vs => vs = ofList (triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ACC) :: acc)
      (fun _ out => out = Val.int (((P / t : ℕ) : ℤ)) ::
        ofList (triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ACC) :: acc)
      (fun _ => 16 * (isz (((P / t : ℕ) : ℤ)) + 1)) :=
    labStepRestore main S1
      (ofList (triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ACC) :: acc) (((P / t : ℕ) : ℤ))
  -- assemble
  have hAB : WordR1 main (pickP 1 ;; tdP) S1 S1
      (fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.int (((P / t : ℕ) : ℤ)) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ => Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1)) +
        Kd * isz (P : ℤ) * isz (t : ℤ)) := WordR1_seq_pp h1 h2
  have hABC : WordR1 main (pickP 1 ;; tdP ;; dupP) S1 S1
      (fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.int (((P / t : ℕ) : ℤ)) :: Val.int (((P / t : ℕ) : ℤ)) ::
        Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ => Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1)) + Kd * isz (P : ℤ) * isz (t : ℤ)
        + Kud * (isz (((P / t : ℕ) : ℤ)) + 1)) := WordR1_seq_pp hAB h3
  have hABCD : WordR1 main (pickP 1 ;; tdP ;; dupP ;; Work.Layout.mvVal 0 1 14 15)
      S1 ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.int (((P / t : ℕ) : ℤ)) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ => Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1)) + Kd * isz (P : ℤ) * isz (t : ℤ)
        + Kud * (isz (((P / t : ℕ) : ℤ)) + 1) + 16 * (isz (((P / t : ℕ) : ℤ)) + 1)) :=
    WordR1_seq_pp hABC h4
  have h5p : WordR1 main (pickP 1 ;; tdP ;; dupP ;; Work.Layout.mvVal 0 1 14 15 ;; consVP)
      S1 ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.cons (Val.int (((P / t : ℕ) : ℤ))) (Val.int (P : ℤ)) ::
        ofList ACC :: acc)
      (fun _ => Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1)) + Kd * isz (P : ℤ) * isz (t : ℤ)
        + Kud * (isz (((P / t : ℕ) : ℤ)) + 1) + 16 * (isz (((P / t : ℕ) : ℤ)) + 1) + Kcv) :=
    WordR1_seq_pp hABCD h5
  have h6p : WordR1 main (pickP 1 ;; tdP ;; dupP ;; Work.Layout.mvVal 0 1 14 15 ;; consVP ;;
        pushP (.int 0)) S1 ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.int 0 :: Val.cons (Val.int (((P / t : ℕ) : ℤ)))
        (Val.int (P : ℤ)) :: ofList ACC :: acc)
      (fun _ => Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1)) + Kd * isz (P : ℤ) * isz (t : ℤ)
        + Kud * (isz (((P / t : ℕ) : ℤ)) + 1) + 16 * (isz (((P / t : ℕ) : ℤ)) + 1) + Kcv
        + 3 * Kpv) := WordR1_seq_pp h5p h6
  have h7p : WordR1 main (pickP 1 ;; tdP ;; dupP ;; Work.Layout.mvVal 0 1 14 15 ;; consVP ;;
        pushP (.int 0) ;; consVP) S1 ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ofList ACC :: acc)
      (fun _ => Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1)) + Kd * isz (P : ℤ) * isz (t : ℤ)
        + Kud * (isz (((P / t : ℕ) : ℤ)) + 1) + 16 * (isz (((P / t : ℕ) : ℤ)) + 1) + Kcv
        + 3 * Kpv + Kcv) := WordR1_seq_pp h6p h7
  have h8p : WordR1 main (pickP 1 ;; tdP ;; dupP ;; Work.Layout.mvVal 0 1 14 15 ;; consVP ;;
        pushP (.int 0) ;; consVP ;; consVP) S1 ((Val.int (((P / t : ℕ) : ℤ))).enc ++ S1)
      (fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = ofList (triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ACC) :: acc)
      (fun _ => Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1)) + Kd * isz (P : ℤ) * isz (t : ℤ)
        + Kud * (isz (((P / t : ℕ) : ℤ)) + 1) + 16 * (isz (((P / t : ℕ) : ℤ)) + 1) + Kcv
        + 3 * Kpv + Kcv + Kcv) := WordR1_seq_pp h7p h8
  have hfull : WordR1 main (crtStepProg pickP tdP dupP consVP pushP) S1 S1
      (fun vs => vs = Val.int (t : ℤ) :: Val.int (P : ℤ) :: ofList ACC :: acc)
      (fun _ out => out = Val.int ((P / t : ℕ) : ℤ) ::
        ofList (triple 0 (((P / t : ℕ) : ℤ)) ((P : ℕ) : ℤ) :: ACC) :: acc)
      (fun _ => Kp * (2 * (isz (t : ℤ) + isz (P : ℤ) + 1)) + Kd * isz (P : ℤ) * isz (t : ℤ)
        + Kud * (isz (((P / t : ℕ) : ℤ)) + 1) + 16 * (isz (((P / t : ℕ) : ℤ)) + 1) + Kcv
        + 3 * Kpv + Kcv + Kcv + 16 * (isz (((P / t : ℕ) : ℤ)) + 1)) := by
    have := WordR1_seq_pp h8p h9
    simpa only [crtStepProg] using this
  -- cost
  refine WordR1_conseq hfull (fun vs h => h) (fun vs out _ h => h) (fun vs _ => ?_)
  have hb := labStep_cost_le Kp Kd Kud Kcv Kpv t.size P.size (P / t).size (size_div_le P t)
  have e1 : isz (t : ℤ) = t.size + 2 := isz_natCast' t
  have e2 : isz (P : ℤ) = P.size + 2 := isz_natCast' P
  have e3 : isz (((P / t : ℕ) : ℤ)) = (P / t).size + 2 := isz_natCast' (P / t)
  rw [e1, e2, e3]
  ring_nf at hb ⊢
  linarith [hb]

end Work.MainP
