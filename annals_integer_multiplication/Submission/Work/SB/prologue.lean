import Mathlib
import Submission.Work.Layout.SB.Toolkit
import Submission.Work.Layout.SB.Specs
import Submission.Work.IntLib.encodeNatBridge

/-!
# Sort-based `applyAlong`: the raw prologue

`Work.Layout.PrologueSpec` (paper §2.3, Lemma 2.11 bookkeeping): from

`int A :: int m :: int n :: int B :: ofList es :: rest`   on stack 0

produce, in linear time,

* stack 0 = `ofList es :: int m :: int B :: int A :: rest`, and
* stack 1 = `int B :: int n ::` (the caller's parked data `X 1`),

leaving every other stack untouched.  The word is

`roll 2 ; mvVal 0 1 14 15 ; roll 2 ; dup ; mvVal 0 1 14 15 ; roll 2 ; roll 3`

at the value level: bring `n` to the top and park it on stack 1, bring `B` to the top, duplicate it,
park one copy above `n`, then rotate `B, A, m, ofList es` into `ofList es, m, B, A`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.SB

open HvdH
open Work.Layout

/-- `mvVal` from `a` to `b` (scratch stacks `c`, `d`) leaves every stack other than `a` and `b`
unchanged (the scratch stacks are restored). -/
theorem prologue_mvVal_frame {main : Cmd} {a b c d : Stk} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : Reg → Glyph}
    {X : Stk → List Glyph} {v : Val} {A B : List Glyph} (ha : X a = v.enc ++ A) (hb : X b = B) :
    ∃ s' n, Ev main (mvVal a b c d) ⟨g, X⟩ s' n ∧ n ≤ 16 * (vsz v + 1) ∧
      s'.stk a = A ∧ s'.stk b = v.enc ++ B ∧
      ∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k := by
  obtain ⟨s', n, h, hn, ha', hb', hc', hd', hf⟩ :=
    mvVal_ev_full hab hac had hbc hbd hcd ha hb
  refine ⟨s', n, h, hn, ha', hb', ?_⟩
  intro k hka hkb
  rcases eq_or_ne k c with rfl | hkc
  · exact hc'
  rcases eq_or_ne k d with rfl | hkd
  · exact hd'
  exact hf k hka hkb hkc hkd

theorem prologue (hK : HvdH.KernelLib) : PrologueSpec := by
  obtain ⟨dupP, Kd, hdup⟩ := hK.dup
  obtain ⟨rollP, Kr, hroll⟩ := hK.roll
  refine ⟨seqs [rollP 2, mvVal 0 1 14 15, rollP 2, dupP, mvVal 0 1 14 15, rollP 2, rollP 3],
    Kr * 40 + Kd * 4 + 100, ?_⟩
  intro main g X R A m n B es rest hX0
  -- (1) `roll 2`: bring `n` to the top.
  obtain ⟨out1, s1, hQ1, hEv1, h0_1, hfr1⟩ :=
    WordR.applyEv (hroll main 2)
      (vs := [Val.int (A:ℤ), Val.int (m:ℤ), Val.int (n:ℤ), Val.int (B:ℤ), ofList es] ++ rest)
      (by simp) (g := g) (X := X) (R := R) hX0
  have hEv1' : Ev main (rollP 2) ⟨g, X⟩ s1
      (Kr * 3 * (vsz (Val.int (A:ℤ)) + (vsz (Val.int (m:ℤ)) + vsz (Val.int (n:ℤ))) + 1)) :=
    hEv1.mono (by
      apply Nat.mul_le_mul_left
      simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega)
  have hout1 : out1 = [Val.int (n:ℤ), Val.int (A:ℤ), Val.int (m:ℤ), Val.int (B:ℤ), ofList es] ++ rest := by
    rw [hQ1]; simp
  have hs1 : s1.stk 0 =
      encs ([Val.int (n:ℤ), Val.int (A:ℤ), Val.int (m:ℤ), Val.int (B:ℤ), ofList es] ++ rest) ++ R := by
    rw [h0_1, hout1]
  -- (2) `mvVal 0 1`: park `n` on stack 1.
  obtain ⟨s2, n2, hEv2, hn2, hA2, hB2, hfr2⟩ :=
    prologue_mvVal_frame (a := 0) (b := 1) (c := 14) (d := 15)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s1.reg) (X := s1.stk) (v := Val.int (n:ℤ))
      (A := encs ([Val.int (A:ℤ), Val.int (m:ℤ), Val.int (B:ℤ), ofList es] ++ rest) ++ R)
      (B := s1.stk 1)
      (by simp only [hs1, encs_cons_tk, List.cons_append, List.nil_append, List.append_assoc]) rfl
  -- (3) `roll 2`: bring `B` to the top.
  obtain ⟨out3, s3, hQ3, hEv3, h0_3, hfr3⟩ :=
    WordR.applyEv (hroll main 2)
      (vs := [Val.int (A:ℤ), Val.int (m:ℤ), Val.int (B:ℤ), ofList es] ++ rest)
      (by simp) (g := s2.reg) (X := s2.stk) (R := R) (by rw [hA2])
  have hEv3' : Ev main (rollP 2) ⟨s2.reg, s2.stk⟩ s3
      (Kr * 3 * (vsz (Val.int (A:ℤ)) + (vsz (Val.int (m:ℤ)) + vsz (Val.int (B:ℤ))) + 1)) :=
    hEv3.mono (by
      apply Nat.mul_le_mul_left
      simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega)
  have hout3 : out3 = [Val.int (B:ℤ), Val.int (A:ℤ), Val.int (m:ℤ), ofList es] ++ rest := by
    rw [hQ3]; simp
  have hs3 : s3.stk 0 =
      encs ([Val.int (B:ℤ), Val.int (A:ℤ), Val.int (m:ℤ), ofList es] ++ rest) ++ R := by
    rw [h0_3, hout3]
  -- (4) `dup`: copy `B`.
  obtain ⟨out4, s4, hQ4, hEv4, h0_4, hfr4⟩ :=
    WordR.applyEv (hdup main)
      (vs := [Val.int (B:ℤ), Val.int (A:ℤ), Val.int (m:ℤ), ofList es] ++ rest)
      (by simp) (g := s3.reg) (X := s3.stk) (R := R) (by rw [hs3])
  obtain ⟨v4, rest4, hvs4, hout4⟩ := hQ4
  have hhead4 : v4 = Val.int (B:ℤ) ∧
      rest4 = [Val.int (A:ℤ), Val.int (m:ℤ), ofList es] ++ rest := by
    have h := hvs4.symm
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact h
  have hEv4' : Ev main dupP ⟨s3.reg, s3.stk⟩ s4 (Kd * (vsz (Val.int (B:ℤ)) + 1)) :=
    hEv4.mono (le_of_eq (by simp))
  have hout4' : out4 =
      [Val.int (B:ℤ), Val.int (B:ℤ), Val.int (A:ℤ), Val.int (m:ℤ), ofList es] ++ rest := by
    rw [hout4, hhead4.1, hhead4.2]
    simp only [List.cons_append, List.nil_append]
  have hs4 : s4.stk 0 =
      encs ([Val.int (B:ℤ), Val.int (B:ℤ), Val.int (A:ℤ), Val.int (m:ℤ), ofList es] ++ rest) ++ R := by
    rw [h0_4, hout4']
  -- (5) `mvVal 0 1`: park the copy of `B` above `n` on stack 1.
  obtain ⟨s5, n5, hEv5, hn5, hA5, hB5, hfr5⟩ :=
    prologue_mvVal_frame (a := 0) (b := 1) (c := 14) (d := 15)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s4.reg) (X := s4.stk) (v := Val.int (B:ℤ))
      (A := encs ([Val.int (B:ℤ), Val.int (A:ℤ), Val.int (m:ℤ), ofList es] ++ rest) ++ R)
      (B := s4.stk 1)
      (by simp only [hs4, encs_cons_tk, List.cons_append, List.nil_append, List.append_assoc]) rfl
  -- (6) `roll 2`.
  obtain ⟨out6, s6, hQ6, hEv6, h0_6, hfr6⟩ :=
    WordR.applyEv (hroll main 2)
      (vs := [Val.int (B:ℤ), Val.int (A:ℤ), Val.int (m:ℤ), ofList es] ++ rest)
      (by simp) (g := s5.reg) (X := s5.stk) (R := R) (by rw [hA5])
  have hEv6' : Ev main (rollP 2) ⟨s5.reg, s5.stk⟩ s6
      (Kr * 3 * (vsz (Val.int (B:ℤ)) + (vsz (Val.int (A:ℤ)) + vsz (Val.int (m:ℤ))) + 1)) :=
    hEv6.mono (by
      apply Nat.mul_le_mul_left
      simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega)
  have hout6 : out6 = [Val.int (m:ℤ), Val.int (B:ℤ), Val.int (A:ℤ), ofList es] ++ rest := by
    rw [hQ6]; simp
  have hs6 : s6.stk 0 =
      encs ([Val.int (m:ℤ), Val.int (B:ℤ), Val.int (A:ℤ), ofList es] ++ rest) ++ R := by
    rw [h0_6, hout6]
  -- (7) `roll 3`: lift `ofList es` over `m, B, A`.
  obtain ⟨out7, s7, hQ7, hEv7, h0_7, hfr7⟩ :=
    WordR.applyEv (hroll main 3)
      (vs := [Val.int (m:ℤ), Val.int (B:ℤ), Val.int (A:ℤ), ofList es] ++ rest)
      (by simp) (g := s6.reg) (X := s6.stk) (R := R) (by rw [hs6])
  have hEv7' : Ev main (rollP 3) ⟨s6.reg, s6.stk⟩ s7
      (Kr * 4 * (vsz (Val.int (m:ℤ)) + (vsz (Val.int (B:ℤ)) +
        (vsz (Val.int (A:ℤ)) + vsz (ofList es))) + 1)) :=
    hEv7.mono (by
      apply Nat.mul_le_mul_left
      simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega)
  have hout7 : out7 = [ofList es, Val.int (m:ℤ), Val.int (B:ℤ), Val.int (A:ℤ)] ++ rest := by
    rw [hQ7]; simp
  have hs7 : s7.stk 0 =
      encs ([ofList es, Val.int (m:ℤ), Val.int (B:ℤ), Val.int (A:ℤ)] ++ rest) ++ R := by
    rw [h0_7, hout7]
  -- assemble the seven steps
  have hEv := Ev.seqs_cons hEv1' (Ev.seqs_cons hEv2 (Ev.seqs_cons hEv3'
      (Ev.seqs_cons hEv4' (Ev.seqs_cons hEv5
        (Ev.seqs_cons (cs := [rollP 3]) hEv6' hEv7')))))
  refine ⟨s7, _, hEv, ?_, ?_, ?_, ?_⟩
  · -- cost bound
    have hb1 : Kr * 3 * (vsz (Val.int (A:ℤ)) + (vsz (Val.int (m:ℤ)) + vsz (Val.int (n:ℤ))) + 1)
        ≤ (Kr * 3) * (isz (A:ℤ) + isz (m:ℤ) + isz (n:ℤ) + isz (B:ℤ) +
          (vsz (ofList es) + 1)) := by
      apply Nat.mul_le_mul_left
      simp only [vsz, Work.IntLib.vsz_int]
      omega
    have hb2 : n2 ≤ 16 * (isz (A:ℤ) + isz (m:ℤ) + isz (n:ℤ) + isz (B:ℤ) +
        (vsz (ofList es) + 1)) := by
      have h := hn2
      simp only [vsz, Work.IntLib.vsz_int] at h
      omega
    have hb3 : Kr * 3 * (vsz (Val.int (A:ℤ)) + (vsz (Val.int (m:ℤ)) + vsz (Val.int (B:ℤ))) + 1)
        ≤ (Kr * 3) * (isz (A:ℤ) + isz (m:ℤ) + isz (n:ℤ) + isz (B:ℤ) +
          (vsz (ofList es) + 1)) := by
      apply Nat.mul_le_mul_left
      simp only [vsz, Work.IntLib.vsz_int]
      omega
    have hb4 : Kd * (vsz (Val.int (B:ℤ)) + 1)
        ≤ Kd * (isz (A:ℤ) + isz (m:ℤ) + isz (n:ℤ) + isz (B:ℤ) +
          (vsz (ofList es) + 1)) := by
      apply Nat.mul_le_mul_left
      simp only [vsz, Work.IntLib.vsz_int]
      omega
    have hb5 : n5 ≤ 16 * (isz (A:ℤ) + isz (m:ℤ) + isz (n:ℤ) + isz (B:ℤ) +
        (vsz (ofList es) + 1)) := by
      have h := hn5
      simp only [vsz, Work.IntLib.vsz_int] at h
      omega
    have hb6 : Kr * 3 * (vsz (Val.int (B:ℤ)) + (vsz (Val.int (A:ℤ)) + vsz (Val.int (m:ℤ))) + 1)
        ≤ (Kr * 3) * (isz (A:ℤ) + isz (m:ℤ) + isz (n:ℤ) + isz (B:ℤ) +
          (vsz (ofList es) + 1)) := by
      apply Nat.mul_le_mul_left
      simp only [vsz, Work.IntLib.vsz_int]
      omega
    have hb7 : Kr * 4 * (vsz (Val.int (m:ℤ)) + (vsz (Val.int (B:ℤ)) +
          (vsz (Val.int (A:ℤ)) + vsz (ofList es))) + 1)
        ≤ (Kr * 4) * (isz (A:ℤ) + isz (m:ℤ) + isz (n:ℤ) + isz (B:ℤ) +
          (vsz (ofList es) + 1)) := by
      apply Nat.mul_le_mul_left
      simp only [vsz, Work.IntLib.vsz_int]
      omega
    nlinarith [hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  · -- stack 0
    rw [hs7]
    simp only [List.cons_append, List.nil_append]
  · -- stack 1
    have h1s1 : s1.stk 1 = X 1 := hfr1 1 (by decide)
    have h3s1 : s3.stk 1 = s2.stk 1 := hfr3 1 (by decide)
    have h4s1 : s4.stk 1 = s3.stk 1 := hfr4 1 (by decide)
    have h6s1 : s6.stk 1 = s5.stk 1 := hfr6 1 (by decide)
    have h7s1 : s7.stk 1 = s6.stk 1 := hfr7 1 (by decide)
    rw [h7s1, h6s1, hB5, h4s1, h3s1, hB2, h1s1]
    simp only [List.append_assoc]
  · -- all other stacks are restored
    intro k hk0 hk1
    rw [hfr7 k hk0, hfr6 k hk0, hfr5 k hk0 hk1, hfr4 k hk0, hfr3 k hk0,
      hfr2 k hk0 hk1, hfr1 k hk0]

end Work.SB
