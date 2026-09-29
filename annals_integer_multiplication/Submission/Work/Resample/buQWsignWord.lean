import Mathlib
import Submission.Work.Resample.interfacesShim
import Submission.Work.Resample.auKit

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-! ## Elementary cost bounds -/

/-- `Kp * (k+1) * S ≤ K * X` when `S ≤ c * X` and `(k+1) * c * Kp ≤ K`. -/
theorem signOp_le {Kp k c S X K : ℕ} (hK : (k + 1) * c * Kp ≤ K) (hS : S ≤ c * X) :
    Kp * (k + 1) * S ≤ K * X := by
  calc Kp * (k + 1) * S = ((k + 1) * Kp) * S := by ring
    _ ≤ ((k + 1) * Kp) * (c * X) := Nat.mul_le_mul_left _ hS
    _ = ((k + 1) * c * Kp) * X := by ring
    _ ≤ K * X := Nat.mul_le_mul_right _ hK

/-- `Kp * S ≤ K * X` when `S ≤ c * X` and `c * Kp ≤ K`. -/
theorem signOp2_le {Kp c S X K : ℕ} (hK : c * Kp ≤ K) (hS : S ≤ c * X) :
    Kp * S ≤ K * X := by
  calc Kp * S ≤ Kp * (c * X) := Nat.mul_le_mul_left _ hS
    _ = (c * Kp) * X := by ring
    _ ≤ K * X := Nat.mul_le_mul_right _ hK

/-! ## `isz` of small constants -/

theorem isz_zero_le : isz (0 : ℤ) ≤ 2 :=
  Work.Fx.isz_le_of_natAbs_lt (a := (0 : ℤ)) (n := 0) (by decide)

theorem isz_one_le : isz (1 : ℤ) ≤ 3 :=
  Work.Fx.isz_le_of_natAbs_lt (a := (1 : ℤ)) (n := 1) (by decide)

theorem isz_negOne_le : isz (-1 : ℤ) ≤ 3 :=
  Work.Fx.isz_le_of_natAbs_lt (a := (-1 : ℤ)) (n := 1) (by decide)

theorem isz_two_le : isz (2 : ℤ) ≤ 4 :=
  Work.Fx.isz_le_of_natAbs_lt (a := (2 : ℤ)) (n := 2) (by decide)

/-! ## `pick 1; pick 1` -/

/-- Two `pick 1` steps: the window `[A, B]` becomes `[A, B, A, B]` (entries `0, 1` are copies). -/
theorem pipePick2 (KL : HvdH.KernelLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (A B : HvdH.Val),
      Pipe main q [A, B] [A, B, A, B] (K * (vsz A + vsz B + 1)) := by
  obtain ⟨pickP, Kpick, hpick⟩ := KL.pick
  refine ⟨.seq (pickP 1) (pickP 1), 4 * Kpick, ?_⟩
  intro main A B
  have h1 : Pipe main (pickP 1) [A, B] [B, A, B]
      (Kpick * (1 + 1) * (Work.Fx.szl (([A, B] : List HvdH.Val).take (1 + 1)) + 1)) :=
    Pipe.pick main hpick (k := 1) (A := ([A, B] : List HvdH.Val)) (by simp)
  have h2 : Pipe main (pickP 1) [B, A, B] [A, B, A, B]
      (Kpick * (1 + 1) * (Work.Fx.szl (([B, A, B] : List HvdH.Val).take (1 + 1)) + 1)) :=
    Pipe.pick main hpick (k := 1) (A := ([B, A, B] : List HvdH.Val)) (by simp)
  refine Pipe.le (Pipe.comp h1 h2) ?_
  have e1 : Work.Fx.szl (([A, B] : List HvdH.Val).take (1 + 1)) + 1 = vsz A + vsz B + 1 := by
    simp only [Work.Fx.szl, List.take_succ_cons, List.take_zero, List.take_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  have e2 : Work.Fx.szl (([B, A, B] : List HvdH.Val).take (1 + 1)) + 1 = vsz A + vsz B + 1 := by
    simp only [Work.Fx.szl, List.take_succ_cons, List.take_zero, List.take_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  rw [e1, e2]
  calc Kpick * (1 + 1) * (vsz A + vsz B + 1) + Kpick * (1 + 1) * (vsz A + vsz B + 1)
      = 4 * Kpick * (vsz A + vsz B + 1) := by ring
    _ ≤ 4 * Kpick * (vsz A + vsz B + 1) := le_rfl

/-! ## the rotation `[C, A, B] ↦ [A, B, C]` -/

/-- Two `roll 2` steps rotate the window `[C, A, B]` into `[A, B, C]`. -/
theorem pipeRot3 (KL : HvdH.KernelLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (A B C : HvdH.Val),
      Pipe main q [C, A, B] [A, B, C] (K * (vsz A + vsz B + vsz C + 1)) := by
  obtain ⟨rollP, Kroll, hroll⟩ := KL.roll
  refine ⟨.seq (rollP 2) (rollP 2), 6 * Kroll, ?_⟩
  intro main A B C
  have h1 : Pipe main (rollP 2) [C, A, B] [B, C, A]
      (Kroll * (2 + 1) * (Work.Fx.szl (([C, A, B] : List HvdH.Val).take (2 + 1)) + 1)) :=
    Pipe.roll main hroll (k := 2) (A := ([C, A, B] : List HvdH.Val)) (by simp)
  have h2 : Pipe main (rollP 2) [B, C, A] [A, B, C]
      (Kroll * (2 + 1) * (Work.Fx.szl (([B, C, A] : List HvdH.Val).take (2 + 1)) + 1)) :=
    Pipe.roll main hroll (k := 2) (A := ([B, C, A] : List HvdH.Val)) (by simp)
  refine Pipe.le (Pipe.comp h1 h2) ?_
  have e1 : Work.Fx.szl (([C, A, B] : List HvdH.Val).take (2 + 1)) + 1
      = vsz A + vsz B + vsz C + 1 := by
    simp only [Work.Fx.szl, List.take_succ_cons, List.take_zero, List.take_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  have e2 : Work.Fx.szl (([B, C, A] : List HvdH.Val).take (2 + 1)) + 1
      = vsz A + vsz B + vsz C + 1 := by
    simp only [Work.Fx.szl, List.take_succ_cons, List.take_zero, List.take_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] <;> omega
  rw [e1, e2]
  calc Kroll * (2 + 1) * (vsz A + vsz B + vsz C + 1)
        + Kroll * (2 + 1) * (vsz A + vsz B + vsz C + 1)
      = 6 * Kroll * (vsz A + vsz B + vsz C + 1) := by ring
    _ ≤ 6 * Kroll * (vsz A + vsz B + vsz C + 1) := le_rfl

/-! ## the core: sign comparison of the two values -/

/-- The sign-comparison word: on the window `[int a, int b]` it leaves the single value
`int (2 * (if (a < 0) = (b < 0) then 1 else 0) - 1)`, at cost linear in `isz a + isz b`. -/
theorem signCmpPipe (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a b : ℤ),
      Pipe main q [Val.int a, Val.int b]
        [Val.int (2 * (if (if a < 0 then (1 : ℤ) else 0) =
          (if b < 0 then (1 : ℤ) else 0) then 1 else 0) - 1)]
        (K * (isz a + isz b + 1)) := by
  obtain ⟨rollP, Kroll, hroll⟩ := KL.roll
  obtain ⟨swapP, Kswap, hswap⟩ := KL.swap
  obtain ⟨pushP, Kpush, hpush⟩ := KL.pushVal
  obtain ⟨ltP, Klt, hlt⟩ := IL.lt
  obtain ⟨eqP, Keq, heq⟩ := IL.eq
  obtain ⟨mulP, Kmul, hmul⟩ := IL.mulS
  obtain ⟨addP, Kadd, hadd⟩ := IL.add
  let Ksum : ℕ := Kroll + Kswap + Kpush + Klt + Keq + Kmul + Kadd + 1
  let KS : ℕ := 1000 * Ksum
  refine ⟨.seq (pushP (.int 0)) (.seq (rollP 1) (.seq ltP (.seq (pushP (.int 0)) (.seq (rollP 2)
    (.seq ltP (.seq swapP (.seq eqP (.seq (pushP (.int 2)) (.seq mulP (.seq (pushP (.int (-1)))
    addP)))))))))), 60 * KS, ?_⟩
  intro main a b
  let sa : ℤ := if a < 0 then (1 : ℤ) else 0
  let sb : ℤ := if b < 0 then (1 : ℤ) else 0
  let e : ℤ := if sa = sb then (1 : ℤ) else 0
  let Y : ℕ := a.natAbs.size + b.natAbs.size + 1
  have hisza : isz a = a.natAbs.size + 2 := rfl
  have hiszb : isz b = b.natAbs.size + 2 := rfl
  have h0isz : isz (0 : ℤ) ≤ 2 := isz_zero_le
  have h1isz : isz (1 : ℤ) ≤ 3 := isz_one_le
  have hneg1isz : isz (-1 : ℤ) ≤ 3 := isz_negOne_le
  have h2isz : isz (2 : ℤ) ≤ 4 := isz_two_le
  have hsa3 : isz sa ≤ 3 := by
    dsimp only [sa]
    by_cases h : a < 0
    · rw [if_pos h]; exact h1isz
    · rw [if_neg h]; exact le_trans h0isz (by norm_num)
  have hsb3 : isz sb ≤ 3 := by
    dsimp only [sb]
    by_cases h : b < 0
    · rw [if_pos h]; exact h1isz
    · rw [if_neg h]; exact le_trans h0isz (by norm_num)
  have he3 : isz e ≤ 3 := by
    dsimp only [e]
    by_cases h : sa = sb
    · rw [if_pos h]; exact h1isz
    · rw [if_neg h]; exact le_trans h0isz (by norm_num)
  have he4 : isz (2 * e) ≤ 4 := by
    dsimp only [e]
    by_cases h : sa = sb
    · rw [if_pos h]
      rw [show (2 : ℤ) * 1 = 2 from by norm_num]
      exact h2isz
    · rw [if_neg h]
      rw [show (2 : ℤ) * 0 = 0 from by norm_num]
      exact le_trans h0isz (by norm_num)
  have s1 : Pipe main (pushP (.int 0)) [Val.int a, Val.int b] [Val.int 0, Val.int a, Val.int b]
      (KS * Y) :=
    Pipe.le (Pipe.pushOnAny (hpush main (.int (0 : ℤ))))
      (signOp2_le (c := 3) (by dsimp only [KS, Ksum]; omega)
        (by rw [Work.Fx.vsz_int]; dsimp only [Y]; omega))
  have s2 : Pipe main (rollP 1) [Val.int 0, Val.int a, Val.int b] [Val.int a, Val.int 0, Val.int b]
      (KS * Y) :=
    Pipe.le (Pipe.roll main hroll (k := 1)
        (A := ([Val.int 0, Val.int a, Val.int b] : List HvdH.Val)) (by simp))
      (signOp_le (c := 6) (by dsimp only [KS, Ksum]; omega)
        (by
          simp only [Work.Fx.szl, Work.Fx.vsz_int, List.take_succ_cons, List.take_zero,
            List.take_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          dsimp only [Y]
          omega))
  have s3 : Pipe main ltP [Val.int a, Val.int 0, Val.int b] [Val.int sa, Val.int b]
      (KS * Y) :=
    Pipe.le (Pipe.appendTail [Val.int b] (Pipe.binOp (hlt main) (a := a) (b := (0 : ℤ)) trivial))
      (signOp2_le (c := 5) (by dsimp only [KS, Ksum]; omega)
        (by dsimp only [Y]; omega))
  have s4 : Pipe main (pushP (.int 0)) [Val.int sa, Val.int b] [Val.int 0, Val.int sa, Val.int b]
      (KS * Y) :=
    Pipe.le (Pipe.pushOnAny (hpush main (.int (0 : ℤ))))
      (signOp2_le (c := 3) (by dsimp only [KS, Ksum]; omega)
        (by rw [Work.Fx.vsz_int]; dsimp only [Y]; omega))
  have s5 : Pipe main (rollP 2) [Val.int 0, Val.int sa, Val.int b] [Val.int b, Val.int 0, Val.int sa]
      (KS * Y) :=
    Pipe.le (Pipe.roll main hroll (k := 2)
        (A := ([Val.int 0, Val.int sa, Val.int b] : List HvdH.Val)) (by simp))
      (signOp_le (c := 10) (by dsimp only [KS, Ksum]; omega)
        (by
          simp only [Work.Fx.szl, Work.Fx.vsz_int, List.take_succ_cons, List.take_zero,
            List.take_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          dsimp only [Y]
          omega))
  have s6 : Pipe main ltP [Val.int b, Val.int 0, Val.int sa] [Val.int sb, Val.int sa]
      (KS * Y) :=
    Pipe.le (Pipe.appendTail [Val.int sa] (Pipe.binOp (hlt main) (a := b) (b := (0 : ℤ)) trivial))
      (signOp2_le (c := 5) (by dsimp only [KS, Ksum]; omega)
        (by dsimp only [Y]; omega))
  have s7 : Pipe main swapP [Val.int sb, Val.int sa] [Val.int sa, Val.int sb] (KS * Y) :=
    Pipe.le (Pipe.swap main hswap (.int sb) (.int sa))
      (signOp2_le (c := 10) (by dsimp only [KS, Ksum]; omega)
        (by rw [Work.Fx.vsz_int, Work.Fx.vsz_int]; dsimp only [Y]; omega))
  have s8 : Pipe main eqP [Val.int sa, Val.int sb] [Val.int e] (KS * Y) :=
    Pipe.le (Pipe.binOp (heq main) (a := sa) (b := sb) trivial)
      (signOp2_le (c := 10) (by dsimp only [KS, Ksum]; omega)
        (by dsimp only [Y]; omega))
  have s9 : Pipe main (pushP (.int 2)) [Val.int e] [Val.int 2, Val.int e] (KS * Y) :=
    Pipe.le (Pipe.pushOnAny (hpush main (.int (2 : ℤ))))
      (signOp2_le (c := 6) (by dsimp only [KS, Ksum]; omega)
        (by rw [Work.Fx.vsz_int]; dsimp only [Y]; omega))
  have s10 : Pipe main mulP [Val.int 2, Val.int e] [Val.int (2 * e)] (KS * Y) :=
    Pipe.le (Pipe.binOp (hmul main) (a := (2 : ℤ)) (b := e) trivial)
      (by
        have h1 : Kmul * isz (2 : ℤ) ≤ Kmul * 4 := Nat.mul_le_mul_left _ h2isz
        have h2 : isz e ≤ 3 := he3
        have h3 : 1 ≤ Y := by dsimp only [Y]; omega
        calc Kmul * isz (2 : ℤ) * isz e ≤ (Kmul * 4) * 3 := Nat.mul_le_mul h1 h2
          _ = 12 * Kmul := by ring
          _ = 12 * Kmul * 1 := by ring
          _ ≤ 12 * Kmul * Y := Nat.mul_le_mul_left _ h3
          _ ≤ KS * Y := Nat.mul_le_mul_right _ (by dsimp only [KS, Ksum]; omega))
  have s11 : Pipe main (pushP (.int (-1))) [Val.int (2 * e)] [Val.int (-1), Val.int (2 * e)]
      (KS * Y) :=
    Pipe.le (Pipe.pushOnAny (hpush main (.int (-1 : ℤ))))
      (signOp2_le (c := 5) (by dsimp only [KS, Ksum]; omega)
        (by rw [Work.Fx.vsz_int]; dsimp only [Y]; omega))
  have s12 : Pipe main addP [Val.int (-1), Val.int (2 * e)] [Val.int (2 * e - 1)] (KS * Y) := by
    refine Pipe.le (Pipe.rw (Pipe.binOp (hadd main) (a := (-1 : ℤ)) (b := 2 * e) trivial) ?_)
      (signOp2_le (c := 10) (by dsimp only [KS, Ksum]; omega)
        (by dsimp only [Y]; omega))
    rw [show (-1 : ℤ) + 2 * e = 2 * e - 1 from by ring]
  have hchain : Pipe main _
      [Val.int a, Val.int b]
      [Val.int (2 * e - 1)]
      (KS * Y + (KS * Y + (KS * Y + (KS * Y + (KS * Y + (KS * Y + (KS * Y + (KS * Y +
        (KS * Y + (KS * Y + (KS * Y + KS * Y))))))))))) :=
    Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6
      (Pipe.comp s7 (Pipe.comp s8 (Pipe.comp s9 (Pipe.comp s10 (Pipe.comp s11 s12))))))))))
  refine Pipe.le hchain ?_
  have h12 : KS * Y + (KS * Y + (KS * Y + (KS * Y + (KS * Y + (KS * Y + (KS * Y + (KS * Y +
      (KS * Y + (KS * Y + (KS * Y + KS * Y)))))))))) = 12 * (KS * Y) := by ring
  rw [h12]
  have hY : Y ≤ isz a + isz b + 1 := by dsimp only [Y, HvdH.isz]; omega
  calc 12 * (KS * Y) = (12 * KS) * Y := by ring
    _ ≤ (12 * KS) * (isz a + isz b + 1) := Nat.mul_le_mul_left _ hY
    _ ≤ (60 * KS) * (isz a + isz b + 1) := Nat.mul_le_mul_right _ (by omega)


/-! ## the target: sign comparison preserving both operands -/

theorem buQWsignWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (a b : ℤ) (R : List HvdH.Val),
      HvdH.WordR main q
        (fun vs => vs = HvdH.Val.int a :: HvdH.Val.int b :: R)
        (fun _ out => out = HvdH.Val.int a :: HvdH.Val.int b ::
          HvdH.Val.int (2 * (if (if a < 0 then (1 : ℤ) else 0) =
            (if b < 0 then (1 : ℤ) else 0) then 1 else 0) - 1) :: R)
        (fun _ => K * (a.natAbs.size + b.natAbs.size + 1)) := by
  obtain ⟨q2, K2, hq2⟩ := pipePick2 KL
  obtain ⟨qc, Kc, hqc⟩ := signCmpPipe KL IL
  obtain ⟨q3, K3, hq3⟩ := pipeRot3 KL
  let KS : ℕ := 1000 * (K2 + Kc + K3 + 1)
  refine ⟨.seq q2 (.seq qc q3), 3 * KS, ?_⟩
  intro main a b R
  let sa : ℤ := if a < 0 then (1 : ℤ) else 0
  let sb : ℤ := if b < 0 then (1 : ℤ) else 0
  let res : ℤ := 2 * (if sa = sb then (1 : ℤ) else 0) - 1
  let Y : ℕ := a.natAbs.size + b.natAbs.size + 1
  have hres3 : isz res ≤ 3 := by
    dsimp only [res, sa, sb]
    by_cases h : (if a < 0 then (1 : ℤ) else 0) = (if b < 0 then (1 : ℤ) else 0)
    · rw [if_pos h]
      rw [show (2 : ℤ) * 1 - 1 = 1 from by norm_num]
      exact isz_one_le
    · rw [if_neg h]
      rw [show (2 : ℤ) * 0 - 1 = -1 from by norm_num]
      exact isz_negOne_le
  have hS6 : isz a + isz b + 1 ≤ 6 * Y := by dsimp only [Y, HvdH.isz]; omega
  have hS6v : vsz (Val.int a) + vsz (Val.int b) + 1 ≤ 6 * Y := by
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int]; exact hS6
  have hS10 : vsz (Val.int a) + vsz (Val.int b) + vsz (Val.int res) + 1 ≤ 10 * Y := by
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int, Work.Fx.vsz_int]
    have h3 : isz res ≤ 3 := hres3
    dsimp only [Y, HvdH.isz] at h3 ⊢
    omega
  have p2 : Pipe main q2 [Val.int a, Val.int b] [Val.int a, Val.int b, Val.int a, Val.int b]
      (KS * Y) :=
    Pipe.le (hq2 main (.int a) (.int b))
      (signOp2_le (c := 6) (by dsimp only [KS]; omega) hS6v)
  have pc : Pipe main qc [Val.int a, Val.int b] [Val.int res] (KS * Y) :=
    Pipe.le (hqc main a b)
      (signOp2_le (c := 6) (by dsimp only [KS]; omega) hS6)
  have htail : Pipe main qc [Val.int a, Val.int b, Val.int a, Val.int b]
      [Val.int res, Val.int a, Val.int b] (KS * Y) :=
    Pipe.appendTail [Val.int a, Val.int b] pc
  have p3 : Pipe main q3 [Val.int res, Val.int a, Val.int b]
      [Val.int a, Val.int b, Val.int res] (KS * Y) :=
    Pipe.le (hq3 main (.int a) (.int b) (.int res))
      (signOp2_le (c := 10) (by dsimp only [KS]; omega) hS10)
  have hcomp : Pipe main (.seq q2 (.seq qc q3)) [Val.int a, Val.int b]
      [Val.int a, Val.int b, Val.int res] (KS * Y + (KS * Y + KS * Y)) :=
    Pipe.comp p2 (Pipe.comp htail p3)
  have hW := hcomp R
  refine KL.conseq main (.seq q2 (.seq qc q3)) _ _ _ _ _ _ hW
    (fun vs h => ?_) (fun vs out _ h => ?_) (fun vs _ => ?_)
  · rw [h]; rfl
  · rw [h]; rfl
  · have h3 : KS * Y + (KS * Y + KS * Y) = (3 * KS) * Y := by ring
    have hYd : Y = a.natAbs.size + b.natAbs.size + 1 := rfl
    rw [h3, hYd]

end Work.Resample
