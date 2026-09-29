import Mathlib
import Submission.Work.Resample.lamDefs
import Submission.Work.Resample.sigFmod
import Submission.Work.Resample.sigSizes
import Submission.Work.Params.steps
import Submission.Work.Params.sizearith
import Submission.Work.IntLib.encodeNatBridge

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open HvdH

namespace Work.Resample


/-! ### helpers -/

theorem sr_vsz_int (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

theorem sr_budget_const {Kc X c : ℕ} (hX : 1 ≤ X) (hc : c ≤ Kc) : c ≤ Kc * X * X := by
  have h1 : 0 < X * X := Nat.mul_pos (by omega) (by omega)
  calc c ≤ Kc := hc
    _ ≤ Kc * (X * X) := Nat.le_mul_of_pos_right Kc h1
    _ = Kc * X * X := (Nat.mul_assoc Kc X X).symm

theorem sr_mul_le_budget {Kc X c M : ℕ} (hc : c ≤ Kc) (hM : M ≤ X * X) : c * M ≤ Kc * X * X := by
  calc c * M ≤ Kc * M := Nat.mul_le_mul_right M hc
    _ ≤ Kc * (X * X) := Nat.mul_le_mul_left Kc hM
    _ = Kc * X * X := (Nat.mul_assoc Kc X X).symm

theorem sr_lin_le_sq {X n : ℕ} (h : n ≤ 3 * X) (hX : 3 ≤ X) : n ≤ X * X :=
  le_trans h (Nat.mul_le_mul_right X hX)

theorem sr_le_sq_self {X : ℕ} (hX : 1 ≤ X) : X ≤ X * X := by
  calc X = X * 1 := by ring
    _ ≤ X * X := Nat.mul_le_mul_left X hX

end Work.Resample

namespace Work.Resample

open HvdH
open Work.Params

theorem sigRecWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (s t k : ℕ) (hst : s < t) (hk : k < t),
      ∀ rest : List HvdH.Val, HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.cons (HvdH.Val.int (k : ℤ)) (HvdH.Val.int 0),
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest)
        (fun vs out => vs = [HvdH.Val.cons (HvdH.Val.int (k : ℤ)) (HvdH.Val.int 0),
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest ∧
          out = [HvdH.Val.cons (HvdH.Val.int ((Work.Resample.egSigT s t k : ℕ) : ℤ))
            (HvdH.Val.int (k : ℤ)), HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest)
        (fun _ => K * (HvdH.isz (k : ℤ) + HvdH.isz (s : ℤ) + HvdH.isz (t : ℤ) + 1) ^ K) := by
  obtain ⟨uProg, uK, uSpec⟩ := KL.unconsV
  obtain ⟨cProg, cK, cSpec⟩ := KL.consV
  obtain ⟨dProg, dK, dSpec⟩ := KL.drop
  obtain ⟨pkProg, pkK, pkSpec⟩ := KL.pick
  obtain ⟨rlProg, rlK, rlSpec⟩ := KL.roll
  obtain ⟨msProg, msK, msSpec⟩ := IL.mulS
  obtain ⟨ngProg, ngK, ngSpec⟩ := IL.neg
  obtain ⟨fmProg, fmK, fmSpec⟩ := IL.fmod
  set Kc : ℕ := 100 * (uK + cK + dK + pkK + rlK + msK + ngK + fmK + 1) with hKcdef
  let prg : Cmd := .seq uProg (.seq (pkProg 3) (.seq (pkProg 3) (.seq (pkProg 2) (.seq msProg
    (.seq ngProg (.seq fmProg (.seq (rlProg 2) (.seq dProg cProg))))))))
  refine ⟨prg, 10 * Kc + 3, ?_⟩
  intro main s t k hst hk rest
  have ht : 0 < t := by omega
  have htZ : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
  have hZeq : ((egSigT s t k : ℕ) : ℤ) = Int.fmod (-((k : ℤ) * (s : ℤ))) (t : ℤ) := sigFmod s t k ht
  set sg : ℤ := Int.fmod (-((k : ℤ) * (s : ℤ))) (t : ℤ) with hsg
  set A : ℕ := isz (k : ℤ) with hA
  set B : ℕ := isz (s : ℤ) with hB
  set C : ℕ := isz (t : ℤ) with hC
  set X : ℕ := A + B + C + 1 with hX
  set Y : ℕ := Kc * X * X with hY
  have hA2 : 2 ≤ A := by rw [hA]; exact sigSizes.2.2.2.1 (k : ℤ)
  have h0 : isz (0 : ℤ) = 2 := sigSizes.2.2.2.2
  have hX1 : 1 ≤ X := by omega
  have hX3 : 3 ≤ X := by omega
  have hAX : A ≤ X := by omega
  have hBX : B ≤ X := by omega
  have hCX : C ≤ X := by omega
  have hksX : isz ((k : ℤ) * (s : ℤ)) ≤ X := by
    have h := sigSizes.1 (k : ℤ) (s : ℤ)
    omega
  have hσX : isz sg ≤ X := by
    rw [hsg]
    have h := sigSizes.2.2.1 (-((k : ℤ) * (s : ℤ))) (t : ℤ) htZ
    omega
  have hneg : isz (-((k : ℤ) * (s : ℤ))) ≤ X := by
    rw [sigSizes.2.1]; exact hksX
  have hKu : uK ≤ Kc := by omega
  have hKc4pk : 4 * pkK ≤ Kc := by omega
  have hKc3pk : 3 * pkK ≤ Kc := by omega
  have hKms : msK ≤ Kc := by omega
  have hKng : ngK ≤ Kc := by omega
  have hKfm : fmK ≤ Kc := by omega
  have hK3rl : 3 * rlK ≤ Kc := by omega
  have hKd : dK ≤ Kc := by omega
  have hKcK : cK ≤ Kc := by omega
  let S0 : List Val := [Val.cons (Val.int (k : ℤ)) (Val.int 0), Val.int (s : ℤ), Val.int (t : ℤ)]
  let S1 : List Val := [Val.int (k : ℤ), Val.int 0, Val.int (s : ℤ), Val.int (t : ℤ)]
  let S2 : List Val := [Val.int (t : ℤ), Val.int (k : ℤ), Val.int 0, Val.int (s : ℤ), Val.int (t : ℤ)]
  let S3 : List Val := [Val.int (s : ℤ), Val.int (t : ℤ), Val.int (k : ℤ), Val.int 0,
    Val.int (s : ℤ), Val.int (t : ℤ)]
  let S4 : List Val := [Val.int (k : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (k : ℤ),
    Val.int 0, Val.int (s : ℤ), Val.int (t : ℤ)]
  let Bc : List Val := [Val.int (t : ℤ), Val.int (k : ℤ), Val.int 0, Val.int (s : ℤ), Val.int (t : ℤ)]
  let Bc2 : List Val := [Val.int (k : ℤ), Val.int 0, Val.int (s : ℤ), Val.int (t : ℤ)]
  let S5 : List Val := [Val.int ((k : ℤ) * (s : ℤ)), Val.int (t : ℤ), Val.int (k : ℤ),
    Val.int 0, Val.int (s : ℤ), Val.int (t : ℤ)]
  let S6 : List Val := [Val.int (-((k : ℤ) * (s : ℤ))), Val.int (t : ℤ), Val.int (k : ℤ),
    Val.int 0, Val.int (s : ℤ), Val.int (t : ℤ)]
  let S7 : List Val := [Val.int sg, Val.int (k : ℤ), Val.int 0, Val.int (s : ℤ), Val.int (t : ℤ)]
  let S8 : List Val := [Val.int 0, Val.int sg, Val.int (k : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
  let S9 : List Val := [Val.int sg, Val.int (k : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
  let S10 : List Val := [Val.cons (Val.int sg) (Val.int (k : ℤ)), Val.int (s : ℤ), Val.int (t : ℤ)]
  have hlen1 : 3 < (S1 ++ rest).length := by
    rw [List.length_append]
    have h1 : S1.length = 4 := rfl
    omega
  have hlen2 : 3 < (S2 ++ rest).length := by
    rw [List.length_append]
    have h1 : S2.length = 5 := rfl
    omega
  have hlen3 : 2 < (S3 ++ rest).length := by
    rw [List.length_append]
    have h1 : S3.length = 6 := rfl
    omega
  have hlen7 : 2 < (S7 ++ rest).length := by
    rw [List.length_append]
    have h1 : S7.length = 5 := rfl
    omega
  have hc1 : uK ≤ Y := by rw [hY]; exact sr_budget_const hX1 hKu
  have hc2 : pkK * (3 + 1) * (vsh (3 + 1) (S1 ++ rest) + 1) ≤ Y := by
    rw [hY]
    have hv : vsh (3 + 1) (S1 ++ rest) + 1 = X + 2 := by
      have e : S1 ++ rest = Val.int (k : ℤ) :: Val.int 0 :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: rest := rfl
      rw [e]
      simp only [vsh_cons, vsh_zero, sr_vsz_int]
      omega
    rw [hv]
    have hrw : pkK * (3 + 1) * (X + 2) = 4 * pkK * (X + 2) := by ring
    rw [hrw]
    exact sr_mul_le_budget hKc4pk (sr_lin_le_sq (by omega) hX3)
  have hc3 : pkK * (3 + 1) * (vsh (3 + 1) (S2 ++ rest) + 1) ≤ Y := by
    rw [hY]
    have hv : vsh (3 + 1) (S2 ++ rest) + 1 = X + 2 := by
      have e : S2 ++ rest = Val.int (t : ℤ) :: Val.int (k : ℤ) :: Val.int 0 :: Val.int (s : ℤ)
        :: Val.int (t : ℤ) :: rest := rfl
      rw [e]
      simp only [vsh_cons, vsh_zero, sr_vsz_int]
      omega
    rw [hv]
    have hrw : pkK * (3 + 1) * (X + 2) = 4 * pkK * (X + 2) := by ring
    rw [hrw]
    exact sr_mul_le_budget hKc4pk (sr_lin_le_sq (by omega) hX3)
  have hc4 : pkK * (2 + 1) * (vsh (2 + 1) (S3 ++ rest) + 1) ≤ Y := by
    rw [hY]
    have hv : vsh (2 + 1) (S3 ++ rest) + 1 = X := by
      have e : S3 ++ rest = Val.int (s : ℤ) :: Val.int (t : ℤ) :: Val.int (k : ℤ) :: Val.int 0
        :: Val.int (s : ℤ) :: Val.int (t : ℤ) :: rest := rfl
      rw [e]
      simp only [vsh_cons, vsh_zero, sr_vsz_int]
      omega
    rw [hv]
    have hrw : pkK * (2 + 1) * X = 3 * pkK * X := by ring
    rw [hrw]
    exact sr_mul_le_budget hKc3pk (sr_le_sq_self hX1)
  have hc5 : msK * isz (k : ℤ) * isz (s : ℤ) ≤ Y := by
    rw [hY]
    have hM : isz (k : ℤ) * isz (s : ℤ) ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
    have hrw : msK * isz (k : ℤ) * isz (s : ℤ) = msK * (isz (k : ℤ) * isz (s : ℤ)) := by ring
    rw [hrw]
    exact sr_mul_le_budget hKms hM
  have hc6 : ngK * isz ((k : ℤ) * (s : ℤ)) ≤ Y := by
    rw [hY]
    exact sr_mul_le_budget hKng (le_trans hksX (sr_le_sq_self hX1))
  have hc7 : fmK * isz (-((k : ℤ) * (s : ℤ))) * isz (t : ℤ) ≤ Y := by
    rw [hY]
    have hM : isz (-((k : ℤ) * (s : ℤ))) * isz (t : ℤ) ≤ X * X :=
      Nat.mul_le_mul hneg (by omega)
    have hrw : fmK * isz (-((k : ℤ) * (s : ℤ))) * isz (t : ℤ) =
        fmK * (isz (-((k : ℤ) * (s : ℤ))) * isz (t : ℤ)) := by ring
    rw [hrw]
    exact sr_mul_le_budget hKfm hM
  have hc8 : rlK * (2 + 1) * (vsh (2 + 1) (S7 ++ rest) + 1) ≤ Y := by
    rw [hY]
    have hv : vsh (2 + 1) (S7 ++ rest) + 1 = isz sg + A + 3 := by
      have e : S7 ++ rest = Val.int sg :: Val.int (k : ℤ) :: Val.int 0 :: Val.int (s : ℤ)
        :: Val.int (t : ℤ) :: rest := rfl
      rw [e]
      simp only [vsh_cons, vsh_zero, sr_vsz_int]
      omega
    rw [hv]
    have hrw : rlK * (2 + 1) * (isz sg + A + 3) = 3 * rlK * (isz sg + A + 3) := by ring
    rw [hrw]
    exact sr_mul_le_budget hK3rl (sr_lin_le_sq (by omega) hX3)
  have hc9 : dK * (vsz (Val.int 0) + 1) ≤ Y := by
    rw [hY]
    have hv : vsz (Val.int 0) = 2 := by rw [sr_vsz_int, h0]
    rw [hv]
    have hrw : dK * (2 + 1) = dK * 3 := by ring
    rw [hrw]
    exact sr_mul_le_budget hKd (sr_lin_le_sq (by omega) hX3)
  have hc10 : cK ≤ Y := by rw [hY]; exact sr_budget_const hX1 hKcK
  have H1 : WordR main uProg (fun vs => vs = S0 ++ rest) (fun _ out => out = S1 ++ rest)
      (fun _ => Y) :=
    unconsVStep (hK := KL) (main := main) (p := uProg) (K0 := uK) (uSpec main)
      (Val.int (k : ℤ)) (Val.int 0) ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest) Y hc1
  have H2 : WordR main (pkProg 3) (fun vs => vs = S1 ++ rest) (fun _ out => out = S2 ++ rest)
      (fun _ => Y) :=
    pickStep (hK := KL) (main := main) (prog := pkProg) (K0 := pkK) (pkSpec main) 3 (S1 ++ rest)
      hlen1 Y hc2
  have H3 : WordR main (pkProg 3) (fun vs => vs = S2 ++ rest) (fun _ out => out = S3 ++ rest)
      (fun _ => Y) :=
    pickStep (hK := KL) (main := main) (prog := pkProg) (K0 := pkK) (pkSpec main) 3 (S2 ++ rest)
      hlen2 Y hc3
  have H4 : WordR main (pkProg 2) (fun vs => vs = S3 ++ rest) (fun _ out => out = S4 ++ rest)
      (fun _ => Y) :=
    pickStep (hK := KL) (main := main) (prog := pkProg) (K0 := pkK) (pkSpec main) 2 (S3 ++ rest)
      hlen3 Y hc4
  have H5 : WordR main msProg (fun vs => vs = S4 ++ rest) (fun _ out => out = S5 ++ rest)
      (fun _ => Y) :=
    binStep (hK := KL) (main := main) (p := msProg) (msSpec main) (k : ℤ) (s : ℤ) (Bc ++ rest)
      trivial Y hc5
  have H6 : WordR main ngProg (fun vs => vs = S5 ++ rest) (fun _ out => out = S6 ++ rest)
      (fun _ => Y) :=
    unStep (hK := KL) (main := main) (p := ngProg) (ngSpec main) ((k : ℤ) * (s : ℤ)) (Bc ++ rest)
      trivial Y hc6
  have H7 : WordR main fmProg (fun vs => vs = S6 ++ rest) (fun _ out => out = S7 ++ rest)
      (fun _ => Y) :=
    binStep (hK := KL) (main := main) (p := fmProg) (fmSpec main) (-((k : ℤ) * (s : ℤ))) (t : ℤ)
      (Bc2 ++ rest) htZ Y hc7
  have H8 : WordR main (rlProg 2) (fun vs => vs = S7 ++ rest) (fun _ out => out = S8 ++ rest)
      (fun _ => Y) :=
    rollStep (hK := KL) (main := main) (prog := rlProg) (K0 := rlK) (rlSpec main) 2 (S7 ++ rest)
      hlen7 Y hc8
  have H9 : WordR main dProg (fun vs => vs = S8 ++ rest) (fun _ out => out = S9 ++ rest)
      (fun _ => Y) :=
    dropStep (hK := KL) (main := main) (p := dProg) (K0 := dK) (dSpec main) (Val.int 0) (S9 ++ rest)
      Y hc9
  have H10 : WordR main cProg (fun vs => vs = S9 ++ rest) (fun _ out => out = S10 ++ rest)
      (fun _ => Y) :=
    consVStep (hK := KL) (main := main) (p := cProg) (K0 := cK) (cSpec main) (Val.int sg)
      (Val.int (k : ℤ)) ([Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest) Y hc10
  have hchain : WordR main prg (fun vs => vs = S0 ++ rest) (fun _ out => out = S10 ++ rest)
      (fun _ => Y + (Y + (Y + (Y + (Y + (Y + (Y + (Y + (Y + Y))))))))) :=
    Work.Params.seqC (hK := KL) H1 (Work.Params.seqC (hK := KL) H2 (Work.Params.seqC (hK := KL) H3
      (Work.Params.seqC (hK := KL) H4 (Work.Params.seqC (hK := KL) H5 (Work.Params.seqC (hK := KL) H6
        (Work.Params.seqC (hK := KL) H7 (Work.Params.seqC (hK := KL) H8 (Work.Params.seqC (hK := KL) H9
          H10))))))))
  have hY10 : Y + (Y + (Y + (Y + (Y + (Y + (Y + (Y + (Y + Y)))))))) ≤ 10 * Y := by omega
  have hAll10 : WordR main prg (fun vs => vs = S0 ++ rest) (fun _ out => out = S10 ++ rest)
      (fun _ => 10 * Y) := Work.Params.conseqC (hK := KL) hchain hY10
  refine KL.conseq main prg
    (fun vs => vs = S0 ++ rest)
    (fun vs => vs = [Val.cons (Val.int (k : ℤ)) (Val.int 0), Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest)
    (fun _ out => out = S10 ++ rest)
    (fun vs out => vs = [Val.cons (Val.int (k : ℤ)) (Val.int 0), Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest ∧
      out = [Val.cons (Val.int ((egSigT s t k : ℕ) : ℤ)) (Val.int (k : ℤ)), Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest)
    (fun _ => 10 * Y) (fun _ => (10 * Kc + 3) * X ^ (10 * Kc + 3))
    hAll10 ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out hvs ho
    refine ⟨hvs, ?_⟩
    rw [ho, hZeq]
  · intro vs _
    rw [hY]
    have hpow : X ^ 2 ≤ X ^ (10 * Kc + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    have hmul : 10 * Kc ≤ 10 * Kc + 3 := by omega
    calc 10 * (Kc * X * X) = 10 * Kc * X ^ 2 := by rw [pow_two]; ring
      _ ≤ (10 * Kc + 3) * X ^ 2 := Nat.mul_le_mul_right _ hmul
      _ ≤ (10 * Kc + 3) * X ^ (10 * Kc + 3) := Nat.mul_le_mul_left _ hpow

end Work.Resample
