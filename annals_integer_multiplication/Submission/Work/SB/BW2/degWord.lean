import Mathlib
import Submission.Work.SB.BW2.Defs
import Submission.Work.SB.BW2.degSize
import Submission.Work.SB.slicesFacts
import Submission.Work.SB.phase1

/-!
# `Work.SB.BW2.degWord` — the degenerate branch `m = 0` of `branchWord2`

`branchWord2` turns `ofList es :: int m :: int B :: int A :: rest` into
`ofList ((slices A m B es).map ofList) :: rest`.  When `m = 0` we have `slices A 0 B es =
List.replicate (A*B) []`, so the answer is `ofList (List.replicate (A*B) .nil) :: rest`.

The word is therefore

`drop ; drop ; mulS ; pushVal .nil ; swap ; replicate (A*B) .nil`

i.e. drop `ofList es` and the (zero) `int m`, multiply the two remaining integers `B` and `A`
(schoolbook, `IntLib.mulS`) to obtain `int (A*B)`, push `nil` and swap so that the value list is
`int (A*B) :: nil :: rest`, which is exactly the input shape of `LayoutLib.replicate`.

The cost of every step is `≤ const * (BIG N L + S A 0 B)`; the integer sizes are controlled by
`Work.SB.BW2.degSize` and the size of `ofList es` is `1` because `es.length = A * 0 * B = 0`.
-/

namespace Work.SB.BW2

open HvdH

/-! ## Elementary size facts for the value list of this branch -/

lemma degWord_vsz_nil : vsz (Val.nil : Val) = 1 := rfl

lemma degWord_vsz_int (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

lemma degWord_vsz_ofList_nil : vsz (ofList ([] : List Val)) = 1 := rfl

lemma degWord_isz_zero : isz ((0 : ℕ) : ℤ) = 2 := by simp [isz]

/-- The statement of the degenerate branch `m = 0` of `branchWord2`. -/
theorem degWord (hK : HvdH.KernelLib) (hI : HvdH.IntLib)
    (hRh : Work.Layout.ReplicateSpec) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (A m B N L : ℕ) (es rest : List HvdH.Val),
      m = 0 → A * B ≤ N → A * m * B ≤ N → es.length = A * m * B →
      (∀ x ∈ es, HvdH.vsz x ≤ L) →
      HvdH.WordR main p (Work.SB.BW2.Pre A m B es rest) (Work.SB.BW2.Post A m B es rest)
        (fun _ => K * Work.SB.BW2.BIG N L + K * Work.SB.BW2.S A m B) := by
  obtain ⟨pDrop, Kd, hDrop⟩ := hK.drop
  obtain ⟨pPush, Kp, hPush⟩ := hK.pushVal
  obtain ⟨pSwap, Ks, hSwap⟩ := hK.swap
  obtain ⟨pMul, Km, hMul⟩ := hI.mulS
  obtain ⟨pRep, Kr, hRep⟩ := hRh
  refine ⟨.seq (.seq (.seq (.seq (.seq pDrop pDrop) pMul) (pPush .nil)) pSwap) pRep,
    32 * (Kd + Km + Kp + Ks + Kr + 1), ?_⟩
  intro main A m B N L es rest hm hAB hAmB hlen hv
  subst hm
  have hes : es = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
  subst es
  intro vs hvs s R hs
  subst hvs
  -- step 1: drop the (empty) original list `ofList es = .nil`
  obtain ⟨o1, s1, n1, hP1, hev1, hle1, hstk1, hfr1⟩ :=
    hDrop main (ofList [] :: .int ((0 : ℕ) : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      (by simp) s R hs
  obtain ⟨_, r1, hv1, ho1⟩ := hP1
  simp only [List.cons.injEq] at hv1
  obtain ⟨-, hr1⟩ := hv1
  have hs1 : s1.stk 0 = encs (.int ((0 : ℕ) : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest) ++ R := by
    rw [hstk1, ho1, ← hr1]
  -- step 2: drop `int m`, which is `int 0`
  obtain ⟨o2, s2, n2, hP2, hev2, hle2, hstk2, hfr2⟩ :=
    hDrop main (.int ((0 : ℕ) : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest) (by simp) s1 R hs1
  obtain ⟨_, r2, hv2, ho2⟩ := hP2
  simp only [List.cons.injEq] at hv2
  obtain ⟨-, hr2⟩ := hv2
  have hs2 : s2.stk 0 = encs (.int (B : ℤ) :: .int (A : ℤ) :: rest) ++ R := by
    rw [hstk2, ho2, ← hr2]
  -- step 3: `int B :: int A :: rest ↦ int (B * A) :: rest`
  obtain ⟨o3, s3, n3, hP3, hev3, hle3, hstk3, hfr3⟩ :=
    hMul main (.int (B : ℤ) :: .int (A : ℤ) :: rest) ⟨(B : ℤ), (A : ℤ), rest, rfl, trivial⟩ s2 R hs2
  obtain ⟨a3, b3, r3, hv3, ho3⟩ := hP3
  simp only [List.cons.injEq, Val.int.injEq] at hv3
  obtain ⟨ha3, hb3, hr3⟩ := hv3
  have hcast : (B : ℤ) * (A : ℤ) = ((A * B : ℕ) : ℤ) := by push_cast; ring
  have ho3' : o3 = .int ((A * B : ℕ) : ℤ) :: rest := by
    rw [ho3, ← ha3, ← hb3, ← hr3]
    exact congrArg (fun z : ℤ => (Val.int z :: rest : List Val)) hcast
  have hs3 : s3.stk 0 = encs (.int ((A * B : ℕ) : ℤ) :: rest) ++ R := by rw [hstk3, ho3']
  -- step 4: push `nil`
  obtain ⟨o4, s4, n4, hP4, hev4, hle4, hstk4, hfr4⟩ :=
    hPush main .nil (.int ((A * B : ℕ) : ℤ) :: rest) (by trivial) s3 R hs3
  have ho4 : o4 = .nil :: .int ((A * B : ℕ) : ℤ) :: rest := hP4
  have hs4 : s4.stk 0 = encs (.nil :: .int ((A * B : ℕ) : ℤ) :: rest) ++ R := by rw [hstk4, ho4]
  -- step 5: swap, giving `int (A * B) :: nil :: rest`
  obtain ⟨o5, s5, n5, hP5, hev5, hle5, hstk5, hfr5⟩ :=
    hSwap main (.nil :: .int ((A * B : ℕ) : ℤ) :: rest) (by simp) s4 R hs4
  obtain ⟨a5, b5, r5, hv5, ho5⟩ := hP5
  simp only [List.cons.injEq] at hv5
  obtain ⟨ha5, hb5a, hb5b⟩ := hv5
  have ho5' : o5 = .int ((A * B : ℕ) : ℤ) :: .nil :: rest := by
    rw [ho5, ← ha5, ← hb5a, ← hb5b]
  have hs5 : s5.stk 0 = encs (.int ((A * B : ℕ) : ℤ) :: .nil :: rest) ++ R := by rw [hstk5, ho5']
  -- step 6: replicate `nil` `A * B` times
  obtain ⟨o6, s6, n6, hP6, hev6, hle6, hstk6, hfr6⟩ :=
    hRep main (A * B) .nil (.int ((A * B : ℕ) : ℤ) :: .nil :: rest) ⟨rest, rfl⟩ s5 R hs5
  obtain ⟨r6, hv6, ho6⟩ := hP6
  simp only [List.cons.injEq] at hv6
  obtain ⟨-, -, h6b⟩ := hv6
  have ho6' : o6 = ofList (List.replicate (A * B) .nil) :: rest := by
    rw [ho6, ← h6b]
  -- size bookkeeping
  obtain ⟨hD, _hAsz, _hBsz, hprod, hABsz, hAB1⟩ := degSize A B N L 0 hAB
  have hprod' : isz (B : ℤ) * isz (A : ℤ) ≤ 4 * (BIG N L + S A 0 B) := by
    rw [Nat.mul_comm]; exact hprod
  -- cost of each step
  have b1 : n1 ≤ 2 * Kd * (BIG N L + S A 0 B) := by
    have h1 : n1 ≤ Kd * 2 := by
      simpa only [List.headD_cons, degWord_vsz_ofList_nil] using hle1
    calc n1 ≤ Kd * 2 := h1
      _ = 2 * Kd * 1 := by ring
      _ ≤ 2 * Kd * (BIG N L + S A 0 B) := Nat.mul_le_mul_left _ hD
  have b2 : n2 ≤ 3 * Kd * (BIG N L + S A 0 B) := by
    have h2 : n2 ≤ Kd * 3 := by
      have h := hle2
      simp only [List.headD_cons, degWord_vsz_int, degWord_isz_zero] at h
      simpa using h
    calc n2 ≤ Kd * 3 := h2
      _ = 3 * Kd * 1 := by ring
      _ ≤ 3 * Kd * (BIG N L + S A 0 B) := Nat.mul_le_mul_left _ hD
  have b3 : n3 ≤ 4 * Km * (BIG N L + S A 0 B) := by
    have h3 : n3 ≤ Km * isz (B : ℤ) * isz (A : ℤ) := hle3
    calc n3 ≤ Km * isz (B : ℤ) * isz (A : ℤ) := h3
      _ = Km * (isz (B : ℤ) * isz (A : ℤ)) := by ring
      _ ≤ Km * (4 * (BIG N L + S A 0 B)) := Nat.mul_le_mul_left _ hprod'
      _ = 4 * Km * (BIG N L + S A 0 B) := by ring
  have b4 : n4 ≤ 2 * Kp * (BIG N L + S A 0 B) := by
    have h4 : n4 ≤ Kp * 2 := by
      simpa only [degWord_vsz_nil] using hle4
    calc n4 ≤ Kp * 2 := h4
      _ = 2 * Kp * 1 := by ring
      _ ≤ 2 * Kp * (BIG N L + S A 0 B) := Nat.mul_le_mul_left _ hD
  have b5 : n5 ≤ 4 * Ks * (BIG N L + S A 0 B) := by
    have h5 : n5 ≤ Ks * (isz ((A * B : ℕ) : ℤ) + 2) := by
      have h := hle5
      simp only [List.getD_cons_zero, List.getD_cons_succ, degWord_vsz_nil, degWord_vsz_int] at h
      have he : Ks * (1 + isz ((A * B : ℕ) : ℤ) + 1) = Ks * (isz ((A * B : ℕ) : ℤ) + 2) := by
        ring
      rwa [he] at h
    have h5b : isz ((A * B : ℕ) : ℤ) + 2 ≤ 4 * (BIG N L + S A 0 B) := by omega
    calc n5 ≤ Ks * (isz ((A * B : ℕ) : ℤ) + 2) := h5
      _ ≤ Ks * (4 * (BIG N L + S A 0 B)) := Nat.mul_le_mul_left _ h5b
      _ = 4 * Ks * (BIG N L + S A 0 B) := by ring
  have b6 : n6 ≤ 5 * Kr * (BIG N L + S A 0 B) := by
    have h6 : n6 ≤ Kr * ((A * B + 1) * 2 + isz ((A * B : ℕ) : ℤ) + 1) := by
      simpa only [degWord_vsz_nil] using hle6
    have h6b : (A * B + 1) * 2 + isz ((A * B : ℕ) : ℤ) + 1 ≤ 5 * (BIG N L + S A 0 B) := by omega
    calc n6 ≤ Kr * ((A * B + 1) * 2 + isz ((A * B : ℕ) : ℤ) + 1) := h6
      _ ≤ Kr * (5 * (BIG N L + S A 0 B)) := Nat.mul_le_mul_left _ h6b
      _ = 5 * Kr * (BIG N L + S A 0 B) := by ring
  refine ⟨o6, s6, ((((n1 + n2) + n3) + n4) + n5) + n6, ?_, ?_, ?_, ?_, ?_⟩
  · -- the output value list is the one required by `Post`
    refine ⟨slices A 0 B [], ?_, rfl⟩
    rw [ho6']
    congr 1
    rw [(Work.SB.slicesFacts A 0 B []).2.2.2.1, List.map_replicate]
    rfl
  · -- evaluation of the assembled program
    exact Eval.seq (Eval.seq (Eval.seq (Eval.seq (Eval.seq hev1 hev2) hev3) hev4) hev5) hev6
  · -- total cost
    have hstep : ((((n1 + n2) + n3) + n4) + n5) + n6 ≤
        (((((2 * Kd) * (BIG N L + S A 0 B) + (3 * Kd) * (BIG N L + S A 0 B))
          + (4 * Km) * (BIG N L + S A 0 B)) + (2 * Kp) * (BIG N L + S A 0 B))
          + (4 * Ks) * (BIG N L + S A 0 B)) + (5 * Kr) * (BIG N L + S A 0 B) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add b1 b2) b3) b4)
        b5) b6
    have hEq : (((((2 * Kd) * (BIG N L + S A 0 B) + (3 * Kd) * (BIG N L + S A 0 B))
          + (4 * Km) * (BIG N L + S A 0 B)) + (2 * Kp) * (BIG N L + S A 0 B))
          + (4 * Ks) * (BIG N L + S A 0 B)) + (5 * Kr) * (BIG N L + S A 0 B)
        = (2 * Kd + 3 * Kd + 4 * Km + 2 * Kp + 4 * Ks + 5 * Kr) * (BIG N L + S A 0 B) := by ring
    have hK2 : 2 * Kd + 3 * Kd + 4 * Km + 2 * Kp + 4 * Ks + 5 * Kr
        ≤ 32 * (Kd + Km + Kp + Ks + Kr + 1) := by nlinarith
    calc ((((n1 + n2) + n3) + n4) + n5) + n6
        ≤ (((((2 * Kd) * (BIG N L + S A 0 B) + (3 * Kd) * (BIG N L + S A 0 B))
          + (4 * Km) * (BIG N L + S A 0 B)) + (2 * Kp) * (BIG N L + S A 0 B))
          + (4 * Ks) * (BIG N L + S A 0 B)) + (5 * Kr) * (BIG N L + S A 0 B) := hstep
      _ = (2 * Kd + 3 * Kd + 4 * Km + 2 * Kp + 4 * Ks + 5 * Kr) * (BIG N L + S A 0 B) := hEq
      _ ≤ (32 * (Kd + Km + Kp + Ks + Kr + 1)) * (BIG N L + S A 0 B) :=
          Nat.mul_le_mul_right _ hK2
      _ = 32 * (Kd + Km + Kp + Ks + Kr + 1) * BIG N L
          + 32 * (Kd + Km + Kp + Ks + Kr + 1) * S A 0 B := by rw [Nat.mul_add]
  · -- the value stack carries the output followed by `R`
    rw [hstk6, ho6']
  · -- the frame: all other stacks are restored
    intro k hk
    rw [hfr6 k hk, hfr5 k hk, hfr4 k hk, hfr3 k hk, hfr2 k hk, hfr1 k hk]

end Work.SB.BW2
