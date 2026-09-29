import Mathlib
import Submission.Work.Resample.buWtKit
import Submission.Work.Resample.buZWalt
import Submission.Work.Resample.buFlgW

/-!
# `Work.Resample.buWtElem`: the element word of the computable weight table

Besides the weight word itself (`Work.Resample.buHornerWord`), the one-dimensional `B̃` resampling
needs, for every output `ℓ` and every shift `h` of the Gaussian window, the integer
`buWt p α s t ℓ h` (`buDefs.lean`): the fixed-point Horner recursion of

`buZ p α s t ℓ h = ⌊2^{auPrec p} · π α² N / s²⌋`, `N = (t h + β_ℓ)² − (β_{ℓ+h})²`, guarded at
`auBnd p = (p+10) 2^{auPrec p}`.

This file builds a single word computing it: from the window `[ℓ, h] ++ buCB p α s t` it produces
`[buWt p α s t ℓ h] ++ buCB p α s t`, at cost `K (p+1)^K`.

The word is the composition of

* `Work.Resample.buZW`   — computes `buZ p α s t ℓ h`,
* `Work.Resample.buFlgW` — computes the guard flag `if Z < auBnd p + 1 then 1 else 0`,
* the `KernelLib.ifZero` branching: flag `0` gives `0` (drop `Z`, push `int 0`), flag `≠ 0` runs
  `−Z`, the Horner word (hypothesis `hornerSpec`) and the final `tdiv` by `2^{auPrec p − p}`.

The costs are absorbed into `K (p+1)^K` by `Work.Resample.buCostSum4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 20000000

namespace Work.Resample

open HvdH
open Work.Fx

/-- The cost arithmetic of the element word: the two delegated words, the branch
`ifZero` overhead and the fourteen uniform one-step budgets are absorbed into
`c1 * (p+1)^4 + (KZ*(p+1)^KZ + (KF*(p+1)^KF + Kh*(p+1)^Kh))`. -/
theorem buCostArith {p Λ KZ KF Kh Kiz n₁ n₂ cb iszF : ℕ}
    (h1 : n₁ ≤ KZ * (p + 1) ^ KZ + KF * (p + 1) ^ KF)
    (h2 : n₂ ≤ Kiz * (iszF + 1) + max (2 * cb) (11 * cb + Kh * (p + 1) ^ Kh))
    (h3 : Kiz * (iszF + 1) ≤ cb)
    (h4 : cb ≤ (Λ * 1000000 ^ 2) * (p + 1) ^ 4) :
    n₁ + n₂ ≤ (14 * Λ * 1000000 ^ 2) * (p + 1) ^ 4 +
      (KZ * (p + 1) ^ KZ + (KF * (p + 1) ^ KF + Kh * (p + 1) ^ Kh)) := by
  have h4' : 14 * cb ≤ (14 * Λ * 1000000 ^ 2) * (p + 1) ^ 4 := by
    have h := Nat.mul_le_mul_left 14 h4
    have he : 14 * ((Λ * 1000000 ^ 2) * (p + 1) ^ 4)
        = (14 * Λ * 1000000 ^ 2) * (p + 1) ^ 4 := by ring
    rwa [he] at h
  have hmax : max (2 * cb) (11 * cb + Kh * (p + 1) ^ Kh)
      ≤ 2 * cb + (11 * cb + Kh * (p + 1) ^ Kh) := by omega
  omega

/-! ## The element word -/

theorem buWtElem (KL : HvdH.KernelLib) (IL : HvdH.IntLib)
    (hornerProg : HvdH.Cmd) (Kh : ℕ)
    (hornerSpec : ∀ (main : HvdH.Cmd) (p : ℕ), 100 ≤ p → ∀ (Z : ℤ),
      Z.natAbs ≤ 2 ^ (11 * p + 210) →
      ∀ rest : List HvdH.Val, HvdH.WordR main hornerProg
        (fun vs => vs = [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] ++ rest)
        (fun vs out => vs = [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.auH p Z (Work.Resample.auNstep p))] ++ rest)
        (fun _ => Kh * (p + 1) ^ Kh)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s)
      (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (ℓ h : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hh : h.natAbs ≤ Work.Resample.egM p α),
      ∀ rest : List HvdH.Val, HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int ℓ, HvdH.Val.int h] ++ Work.Resample.buCB p α s t ++ rest)
        (fun vs out => vs = [HvdH.Val.int ℓ, HvdH.Val.int h] ++ Work.Resample.buCB p α s t ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.buWt p α s t ℓ h)] ++ Work.Resample.buCB p α s t ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨progZ, KZ, hZ⟩ := buZWalt KL IL
  obtain ⟨progF, KF, hF⟩ := buFlgW KL IL
  obtain ⟨negProg, Kneg, hneg⟩ := IL.neg
  obtain ⟨addProg, Kadd, hadd⟩ := IL.add
  obtain ⟨mulProg, Kmul, hmul⟩ := IL.mulS
  obtain ⟨tdivProg, Ktd, htd⟩ := IL.tdiv
  obtain ⟨pow2Prog, Kpw, hpw⟩ := IL.pow2
  obtain ⟨dropProg, Kdr, hdr⟩ := KL.drop
  obtain ⟨pickProg, Kpk, hpk⟩ := KL.pick
  obtain ⟨rollProg, Krl, hrl⟩ := KL.roll
  obtain ⟨pushProg, Kpv, hpv⟩ := KL.pushVal
  obtain ⟨izComb, Kiz, hiz⟩ := KL.ifZero
  let Λ : ℕ := KZ + KF + Kh + Kneg + Kadd + Kmul + Ktd + Kpw + Kdr + Kpk + Krl + Kpv + Kiz + 1
  let K : ℕ := 2 ^ (14 * Λ * 1000000 ^ 2 + 4 + KZ + KZ + KF + KF + Kh + Kh + 20)
  let q1 : Cmd := Cmd.seq dropProg (pushProg (.int 0))
  let q2 : Cmd := Cmd.seq negProg (Cmd.seq (pickProg 1) (Cmd.seq (rollProg 1) (Cmd.seq hornerProg
      (Cmd.seq (pickProg 1) (Cmd.seq (pushProg (.int 2)) (Cmd.seq mulProg
        (Cmd.seq (pushProg (.int 100)) (Cmd.seq addProg (Cmd.seq pow2Prog
          (Cmd.seq (rollProg 1) tdivProg))))))))))
  refine ⟨Cmd.seq (Cmd.seq progZ progF) (izComb q1 q2), K, ?_⟩
  intro main p α s t hs hst hα hp htp hαp ℓ h hℓ hℓs hh rest
  -- the values
  let Zv : ℤ := buZ p α s t ℓ h
  let Fv : ℤ := if Zv < auBnd p + 1 then 1 else 0
  let Yv : ℤ := auH p (-(buZ p α s t ℓ h)) (auNstep p)
  let Dv : ℤ := (2 : ℤ) ^ (2 * p + 100)
  let T0 : List Val := [.int (α : ℤ), .int (s : ℤ), .int (t : ℤ),
    .int (((egM p α : ℕ)) : ℤ), .int (((egN p α s t : ℕ)) : ℤ), .int (auPi p)]
  -- basic bounds
  have hs0 : 0 < s := by omega
  have hsp : s < 2 ^ p := by omega
  have h1p : 1 ≤ p := by omega
  have hαltp : α < p := by
    have h1 : α * 1 ≤ α * α := Nat.mul_le_mul_left α (by omega : 1 ≤ α)
    have h2 : α ≤ α * α := by simpa using h1
    exact lt_of_le_of_lt h2 (by simpa [pow_two] using hαp)
  have hαle : α ≤ 2 ^ p := le_trans (le_of_lt hαltp) (le_of_lt (Nat.lt_two_pow_self (n := p)))
  have hαp' : α ^ 2 ≤ p := le_of_lt hαp
  have hMle : egM p α ≤ 2 ^ p := by
    have h1 := egM_le p α
    have h2 : p + 1 ≤ 2 ^ p := by have := Nat.lt_two_pow_self (n := p); omega
    omega
  -- the size of everything: `≤ buSZ p`
  have hzp : isz ((p : ℤ)) ≤ buSZ p :=
    isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact le_of_lt (Nat.lt_two_pow_self (n := p)))
  have hzα : isz ((α : ℤ)) ≤ buSZ p :=
    isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact hαle)
  have hzs : isz ((s : ℤ)) ≤ buSZ p :=
    isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact le_of_lt hsp)
  have hzt : isz ((t : ℤ)) ≤ buSZ p :=
    isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact le_of_lt htp)
  have hzM : isz ((((egM p α : ℕ)) : ℤ)) ≤ buSZ p :=
    isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact hMle)
  have hzN : isz ((((egN p α s t : ℕ)) : ℤ)) ≤ buSZ p := isz_egN_le p α s t hs0 hsp h1p
  have hzPi : isz (auPi p) ≤ buSZ p := isz_auPi_le_buSZ p
  have hzZ : isz Zv ≤ buSZ p := by
    simp only [Zv]
    exact isz_buZ_le p α s t ℓ h hαp' hαle hs0 hh hsp htp hp
  have hZbig : (-(buZ p α s t ℓ h)).natAbs ≤ 2 ^ (11 * p + 210) :=
    by simpa using natAbs_buZ_le p α s t ℓ h hαp' hαle hs0 hh hsp htp hp
  have hzY : isz Yv ≤ buSZ p := by
    simp only [Yv]
    exact isz_auH_le_buSZ p (-(buZ p α s t ℓ h)) (auNstep p) hp hZbig le_rfl
  have hzD : isz Dv ≤ buSZ p := by
    simp only [Dv]
    refine isz_le_buSZ_11 (A := 11 * p + 210) (by omega) ?_
    rw [Int.natAbs_pow]
    have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
    rw [h2]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzF : isz Fv ≤ buSZ p := by
    simp only [Fv]
    split
    · exact isz_le_buSZ_pow_p (by rw [Int.natAbs_one]; have : 0 < 2 ^ p := pow_pos (by norm_num) p; omega)
    · exact isz_le_buSZ_pow_p (by rw [Int.natAbs_zero]; exact Nat.zero_le _)
  have hz2 : isz ((2 : ℤ)) ≤ buSZ p := by
    refine isz_le_buSZ_pow_p ?_
    have h : ((2 : ℤ)).natAbs = 2 := by norm_num
    rw [h]
    calc (2 : ℕ) ≤ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hz100 : isz ((100 : ℤ)) ≤ buSZ p := by
    refine isz_le_buSZ_pow_p ?_
    have h : ((100 : ℤ)).natAbs = 100 := by norm_num
    rw [h]
    calc (100 : ℕ) ≤ 2 ^ 7 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hz2p : isz ((((2 * p : ℕ)) : ℤ)) ≤ buSZ p := by
    refine isz_le_buSZ_11 (A := p + 1) (by omega) ?_
    rw [Int.natAbs_natCast]
    calc 2 * p ≤ 2 * 2 ^ p := Nat.mul_le_mul_left 2 (le_of_lt (Nat.lt_two_pow_self (n := p)))
      _ = 2 ^ (p + 1) := by rw [pow_succ]; ring
  have hz102p : isz ((((100 + 2 * p : ℕ)) : ℤ)) ≤ buSZ p := by
    refine isz_le_buSZ_11 (A := p + 8) (by omega) ?_
    rw [Int.natAbs_natCast]
    have h := Nat.lt_two_pow_self (n := p)
    have he : 2 ^ (p + 8) = 256 * 2 ^ p := by rw [pow_add, mul_comm]; norm_num
    rw [he]
    nlinarith [h, Nat.zero_le p, hp]
  -- the constants are all `≤ Λ`
  have hΛZ : KZ ≤ Λ := by simp only [Λ]; omega
  have hΛF : KF ≤ Λ := by simp only [Λ]; omega
  have hΛneg : Kneg ≤ Λ := by simp only [Λ]; omega
  have hΛadd : Kadd ≤ Λ := by simp only [Λ]; omega
  have hΛmul : Kmul ≤ Λ := by simp only [Λ]; omega
  have hΛtd : Ktd ≤ Λ := by simp only [Λ]; omega
  have hΛpw : Kpw ≤ Λ := by simp only [Λ]; omega
  have hΛdr : Kdr ≤ Λ := by simp only [Λ]; omega
  have hΛpk : Kpk ≤ Λ := by simp only [Λ]; omega
  have hΛrl : Krl ≤ Λ := by simp only [Λ]; omega
  have hΛpv : Kpv ≤ Λ := by simp only [Λ]; omega
  have hΛiz : Kiz ≤ Λ := by simp only [Λ]; omega
  -- step 1: `buZ`
  have hstep1 : Pipe main progZ ([.int ℓ, .int h] ++ buCB p α s t)
      ([.int Zv] ++ buCB p α s t) (KZ * (p + 1) ^ KZ) :=
    hZ main p α s t hs hst hα hp htp hαp ℓ h hℓ hℓs hh
  -- step 2: the guard flag
  have hstep2 : Pipe main progF ([.int Zv] ++ buCB p α s t)
      ([.int Fv] ++ [.int Zv] ++ buCB p α s t) (KF * (p + 1) ^ KF) :=
    Pipe.appendTail (main := main) (prog := progF)
      (A := [.int (buZ p α s t ℓ h), .int (p : ℤ)])
      (B := [.int (if buZ p α s t ℓ h < auBnd p + 1 then 1 else 0),
        .int (buZ p α s t ℓ h), .int (p : ℤ)])
      T0 (hF main p (buZ p α s t ℓ h) hp hzZ)
  have hstepAB : Pipe main (Cmd.seq progZ progF) ([.int ℓ, .int h] ++ buCB p α s t)
      ([.int Fv] ++ [.int Zv] ++ buCB p α s t) (KZ * (p + 1) ^ KZ + KF * (p + 1) ^ KF) :=
    Pipe.comp hstep1 hstep2
  let cb : ℕ := buSBW p Λ
  let c1 : ℕ := 2 * cb
  let c2 : ℕ := 11 * cb + Kh * (p + 1) ^ Kh
  have hc1sum : cb + cb ≤ c1 := by simp only [c1]; omega
  have hc2sum : 11 * cb + Kh * (p + 1) ^ Kh ≤ c2 := by simp only [c2]; exact le_rfl
  have hc1eq : c1 = 2 * cb := rfl
  have hcbun : ∀ {K v : ℕ}, K ≤ Λ → v ≤ buSZ p → K * v ≤ cb := by
    intro K v hK hv
    have h1 : 1 ≤ buSZ p := by simp only [buSZ]; omega
    have h := le_buSBW_mul hK hv h1
    simpa using h
  have hc2eq : c2 = 11 * cb + Kh * (p + 1) ^ Kh := rfl
  -- branch `flag = 0`: drop `Z`, push `0`
  have hQ1 : Fv = 0 → WordR main q1 (fun vs => vs = [.int Zv] ++ buCB p α s t ++ rest)
      (fun _ out => out = [.int 0] ++ buCB p α s t ++ rest) (fun _ => c1) := by
    intro _
    have hd : Pipe main dropProg [.int Zv] [] cb := by
      have h := Pipe.drop main hdr (.int Zv)
      refine Pipe.le h ?_
      rw [vsz_int]
      exact le_buSBW_one hΛdr hzZ
    have hp0 : Pipe main (pushProg (.int 0)) [] [.int 0] cb := by
      have h := Pipe.pushVal (main := main) hpv (.int 0)
      refine Pipe.le h ?_
      rw [vsz_int]
      refine le_buSBW_one hΛpv ?_
      exact isz_le_buSZ_pow_p (by rw [Int.natAbs_zero]; exact Nat.zero_le _)
    have hc : Pipe main q1 [.int Zv] [.int 0] c1 := by
      exact Pipe.le (Pipe.comp hd hp0) hc1sum
    exact hc (buCB p α s t ++ rest)
  -- branch `flag ≠ 0`: the Horner recursion and the final scaling
  have hQ2 : Fv ≠ 0 → WordR main q2 (fun vs => vs = [.int Zv] ++ buCB p α s t ++ rest)
      (fun _ out => out = [.int (Int.tdiv Yv Dv)] ++ buCB p α s t ++ rest) (fun _ => c2) := by
    intro _
    have s1 : Pipe main negProg ([.int Zv] ++ buCB p α s t) ([.int (-Zv)] ++ buCB p α s t) cb :=
      Pipe.le (Pipe.appendTail (main := main) (prog := negProg) (A := [.int Zv]) (B := [.int (-Zv)])
        (buCB p α s t) (Pipe.unOp (hneg main) (a := Zv) (ha := True.intro)))
        (hcbun hΛneg hzZ)
    have s2 : Pipe main (pickProg 1) ([.int (-Zv)] ++ buCB p α s t)
        ([.int (p : ℤ), .int (-Zv), .int (p : ℤ)] ++ T0) cb := by
      have h0 := Pipe.pickAt (prog := pickProg) (K := Kpk) main hpk
        (A := [.int (-Zv), .int (p : ℤ)]) (k := 1) (v := .int (p : ℤ)) (by simp) (by simp)
      have h1 : Pipe main (pickProg 1) ([.int (-Zv), .int (p : ℤ)] ++ T0)
          ([.int (p : ℤ), .int (-Zv), .int (p : ℤ)] ++ T0)
          (Kpk * 2 * (szl ([.int (-Zv), .int (p : ℤ)].take 2) + 1)) :=
        Pipe.appendTail (main := main) (prog := pickProg 1)
          (A := [.int (-Zv), .int (p : ℤ)]) (B := [.int (p : ℤ), .int (-Zv), .int (p : ℤ)]) T0 h0
      refine Pipe.le h1 ?_
      refine le_buSBW_roll hΛpk (A := [.int (-Zv), .int (p : ℤ)]) (k := 1)
        (by norm_num) (by simp) ?_
      intro v hv
      have hv' : v = .int (-Zv) ∨ v = .int (p : ℤ) := by simpa using hv
      rcases hv' with h | h
      · rw [h, vsz_int, isz_neg]; exact hzZ
      · rw [h, vsz_int]; exact hzp
    have s3 : Pipe main (rollProg 1) ([.int (p : ℤ), .int (-Zv), .int (p : ℤ)] ++ T0)
        ([.int (-Zv), .int (p : ℤ), .int (p : ℤ)] ++ T0) cb := by
      have h0 := Pipe.roll (prog := rollProg) (K := Krl) main hrl
        (A := [.int (p : ℤ), .int (-Zv), .int (p : ℤ)]) (k := 1) (by simp)
      have h1 : Pipe main (rollProg 1) ([.int (p : ℤ), .int (-Zv), .int (p : ℤ)] ++ T0)
          ([.int (-Zv), .int (p : ℤ), .int (p : ℤ)] ++ T0)
          (Krl * 2 * (szl ([.int (p : ℤ), .int (-Zv), .int (p : ℤ)].take 2) + 1)) :=
        Pipe.appendTail (main := main) (prog := rollProg 1)
          (A := [.int (p : ℤ), .int (-Zv), .int (p : ℤ)])
          (B := [.int (-Zv), .int (p : ℤ), .int (p : ℤ)]) T0 h0
      refine Pipe.le h1 ?_
      refine le_buSBW_roll hΛrl (A := [.int (p : ℤ), .int (-Zv), .int (p : ℤ)]) (k := 1)
        (by norm_num) (by simp) ?_
      intro v hv
      have hv' : v = .int (p : ℤ) ∨ v = .int (-Zv) ∨ v = .int (p : ℤ) := by simpa using hv
      rcases hv' with h | h | h
      · rw [h, vsz_int]; exact hzp
      · rw [h, vsz_int, isz_neg]; exact hzZ
      · rw [h, vsz_int]; exact hzp
    have s4 : Pipe main hornerProg ([.int (-Zv), .int (p : ℤ), .int (p : ℤ)] ++ T0)
        ([.int Yv] ++ buCB p α s t) (Kh * (p + 1) ^ Kh) :=
      Pipe.appendTail (main := main) (prog := hornerProg)
        (A := [.int (-Zv), .int (p : ℤ)]) (B := [.int Yv]) (buCB p α s t)
        (Pipe.ofHalves (fun rest' => hornerSpec main p hp (-Zv) hZbig rest'))
    have s5 : Pipe main (pickProg 1) ([.int Yv] ++ buCB p α s t)
        ([.int (p : ℤ), .int Yv, .int (p : ℤ)] ++ T0) cb := by
      have h0 := Pipe.pickAt (prog := pickProg) (K := Kpk) main hpk
        (A := [.int Yv, .int (p : ℤ)]) (k := 1) (v := .int (p : ℤ)) (by simp) (by simp)
      have h1 : Pipe main (pickProg 1) ([.int Yv, .int (p : ℤ)] ++ T0)
          ([.int (p : ℤ), .int Yv, .int (p : ℤ)] ++ T0)
          (Kpk * 2 * (szl ([.int Yv, .int (p : ℤ)].take 2) + 1)) :=
        Pipe.appendTail (main := main) (prog := pickProg 1)
          (A := [.int Yv, .int (p : ℤ)]) (B := [.int (p : ℤ), .int Yv, .int (p : ℤ)]) T0 h0
      refine Pipe.le h1 ?_
      refine le_buSBW_roll hΛpk (A := [.int Yv, .int (p : ℤ)]) (k := 1)
        (by norm_num) (by simp) ?_
      intro v hv
      have hv' : v = .int Yv ∨ v = .int (p : ℤ) := by simpa using hv
      rcases hv' with h | h
      · rw [h, vsz_int]; exact hzY
      · rw [h, vsz_int]; exact hzp
    have s6 : Pipe main (pushProg (.int 2)) ([.int (p : ℤ), .int Yv, .int (p : ℤ)] ++ T0)
        ([.int 2, .int (p : ℤ), .int Yv, .int (p : ℤ)] ++ T0) cb := by
      refine Pipe.le (Pipe.pushOnAny (hpv main (.int 2))) ?_
      rw [vsz_int]
      exact le_buSBW_one hΛpv hz2
    have s7 : Pipe main mulProg ([.int 2, .int (p : ℤ), .int Yv, .int (p : ℤ)] ++ T0)
        ([.int (((2 * p : ℕ)) : ℤ), .int Yv, .int (p : ℤ)] ++ T0) cb := by
      have h0 := Pipe.binOp (hmul main) (a := (2 : ℤ)) (b := (p : ℤ)) True.intro
      have h1 : Pipe main mulProg ([.int (2 : ℤ), .int (p : ℤ)] ++ ([.int Yv, .int (p : ℤ)] ++ T0))
          ([.int ((2 : ℤ) * (p : ℤ))] ++ ([.int Yv, .int (p : ℤ)] ++ T0))
          (Kmul * isz (2 : ℤ) * isz (p : ℤ)) :=
        Pipe.appendTail (main := main) (prog := mulProg)
          (A := [.int (2 : ℤ), .int (p : ℤ)]) (B := [.int ((2 : ℤ) * (p : ℤ))])
          ([.int Yv, .int (p : ℤ)] ++ T0) h0
      have hcast : (2 : ℤ) * (p : ℤ) = (((2 * p : ℕ)) : ℤ) := by push_cast; ring
      have hB : ([.int ((2 : ℤ) * (p : ℤ))] ++ ([.int Yv, .int (p : ℤ)] ++ T0))
          = [.int (((2 * p : ℕ)) : ℤ), .int Yv, .int (p : ℤ)] ++ T0 := by
        rw [hcast]; rfl
      refine Pipe.le (Pipe.rw h1 hB) ?_
      exact le_buSBW_mul hΛmul hz2 hzp
    have s8 : Pipe main (pushProg (.int 100))
        ([.int (((2 * p : ℕ)) : ℤ), .int Yv, .int (p : ℤ)] ++ T0)
        ([.int 100, .int (((2 * p : ℕ)) : ℤ), .int Yv, .int (p : ℤ)] ++ T0) cb := by
      refine Pipe.le (Pipe.pushOnAny (hpv main (.int 100))) ?_
      rw [vsz_int]
      exact le_buSBW_one hΛpv hz100
    have s9 : Pipe main addProg
        ([.int 100, .int (((2 * p : ℕ)) : ℤ), .int Yv, .int (p : ℤ)] ++ T0)
        ([.int (((100 + 2 * p : ℕ)) : ℤ), .int Yv, .int (p : ℤ)] ++ T0) cb := by
      have h0 := Pipe.binOp (hadd main) (a := (100 : ℤ)) (b := (((2 * p : ℕ)) : ℤ)) True.intro
      have h1 : Pipe main addProg
          ([.int (100 : ℤ), .int (((2 * p : ℕ)) : ℤ)] ++ ([.int Yv, .int (p : ℤ)] ++ T0))
          ([.int ((100 : ℤ) + (((2 * p : ℕ)) : ℤ))] ++ ([.int Yv, .int (p : ℤ)] ++ T0))
          (Kadd * (isz (100 : ℤ) + isz (((2 * p : ℕ)) : ℤ))) :=
        Pipe.appendTail (main := main) (prog := addProg)
          (A := [.int (100 : ℤ), .int (((2 * p : ℕ)) : ℤ)])
          (B := [.int ((100 : ℤ) + (((2 * p : ℕ)) : ℤ))])
          ([.int Yv, .int (p : ℤ)] ++ T0) h0
      have hcast : (100 : ℤ) + (((2 * p : ℕ)) : ℤ) = (((100 + 2 * p : ℕ)) : ℤ) := by push_cast; ring
      have hB : ([.int ((100 : ℤ) + (((2 * p : ℕ)) : ℤ))] ++ ([.int Yv, .int (p : ℤ)] ++ T0))
          = [.int (((100 + 2 * p : ℕ)) : ℤ), .int Yv, .int (p : ℤ)] ++ T0 := by
        rw [hcast]; rfl
      refine Pipe.le (Pipe.rw h1 hB) ?_
      exact le_buSBW_two hΛadd hz100 hz2p
    have s10 : Pipe main pow2Prog
        ([.int (((100 + 2 * p : ℕ)) : ℤ), .int Yv, .int (p : ℤ)] ++ T0)
        ([.int Dv, .int Yv, .int (p : ℤ)] ++ T0) cb := by
      have h0 := Pipe.unOp (hpw main) (a := (((100 + 2 * p : ℕ)) : ℤ)) (ha := by positivity)
      have h1 : Pipe main pow2Prog
          ([.int (((100 + 2 * p : ℕ)) : ℤ)] ++ ([.int Yv, .int (p : ℤ)] ++ T0))
          ([.int ((2 : ℤ) ^ ((((100 + 2 * p : ℕ)) : ℤ)).toNat)] ++ ([.int Yv, .int (p : ℤ)] ++ T0))
          (Kpw * (((((100 + 2 * p : ℕ)) : ℤ)).toNat + isz (((100 + 2 * p : ℕ)) : ℤ))) :=
        Pipe.appendTail (main := main) (prog := pow2Prog)
          (A := [.int (((100 + 2 * p : ℕ)) : ℤ)])
          (B := [.int ((2 : ℤ) ^ ((((100 + 2 * p : ℕ)) : ℤ)).toNat)])
          ([.int Yv, .int (p : ℤ)] ++ T0) h0
      have hD : (2 : ℤ) ^ ((((100 + 2 * p : ℕ)) : ℤ)).toNat = Dv := by
        rw [Int.toNat_natCast]
        simp only [Dv]
        rw [Nat.add_comm]
      have hB : ([.int ((2 : ℤ) ^ ((((100 + 2 * p : ℕ)) : ℤ)).toNat)]
            ++ ([.int Yv, .int (p : ℤ)] ++ T0))
          = [.int Dv, .int Yv, .int (p : ℤ)] ++ T0 := by
        rw [hD]; rfl
      refine Pipe.le (Pipe.rw h1 hB) ?_
      rw [Int.toNat_natCast]
      refine le_buSBW_two hΛpw (u := 100 + 2 * p)
        (v := isz (((100 + 2 * p : ℕ)) : ℤ)) ?_ hz102p
      have hp100 : (100 + 2 * p) ≤ buSZ p := by simp only [buSZ]; nlinarith [Nat.zero_le p]
      exact hp100
    have s11 : Pipe main (rollProg 1) ([.int Dv, .int Yv, .int (p : ℤ)] ++ T0)
        ([.int Yv, .int Dv, .int (p : ℤ)] ++ T0) cb := by
      have h0 := Pipe.roll (prog := rollProg) (K := Krl) main hrl
        (A := [.int Dv, .int Yv, .int (p : ℤ)]) (k := 1) (by simp)
      have h1 : Pipe main (rollProg 1) ([.int Dv, .int Yv, .int (p : ℤ)] ++ T0)
          ([.int Yv, .int Dv, .int (p : ℤ)] ++ T0)
          (Krl * 2 * (szl ([.int Dv, .int Yv, .int (p : ℤ)].take 2) + 1)) :=
        Pipe.appendTail (main := main) (prog := rollProg 1)
          (A := [.int Dv, .int Yv, .int (p : ℤ)]) (B := [.int Yv, .int Dv, .int (p : ℤ)]) T0 h0
      refine Pipe.le h1 ?_
      refine le_buSBW_roll hΛrl (A := [.int Dv, .int Yv, .int (p : ℤ)]) (k := 1)
        (by norm_num) (by simp) ?_
      intro v hv
      have hv' : v = .int Dv ∨ v = .int Yv ∨ v = .int (p : ℤ) := by simpa using hv
      rcases hv' with h | h | h
      · rw [h, vsz_int]; exact hzD
      · rw [h, vsz_int]; exact hzY
      · rw [h, vsz_int]; exact hzp
    have s12 : Pipe main tdivProg ([.int Yv, .int Dv, .int (p : ℤ)] ++ T0)
        ([.int (Int.tdiv Yv Dv)] ++ buCB p α s t) cb := by
      have h0 := Pipe.binOp (htd main) (a := Yv) (b := Dv)
        (by simp only [Dv]; exact pow_ne_zero _ (by norm_num))
      have h1 : Pipe main tdivProg ([.int Yv, .int Dv] ++ ([.int (p : ℤ)] ++ T0))
          ([.int (Int.tdiv Yv Dv)] ++ ([.int (p : ℤ)] ++ T0))
          (Ktd * isz Yv * isz Dv) :=
        Pipe.appendTail (main := main) (prog := tdivProg) (A := [.int Yv, .int Dv])
          (B := [.int (Int.tdiv Yv Dv)]) ([.int (p : ℤ)] ++ T0) h0
      exact Pipe.le h1 (le_buSBW_mul hΛtd hzY hzD)
    have hchain : Pipe main q2 ([.int Zv] ++ buCB p α s t)
        ([.int (Int.tdiv Yv Dv)] ++ buCB p α s t) c2 := by
      have h := Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5
        (Pipe.comp s6 (Pipe.comp s7 (Pipe.comp s8 (Pipe.comp s9 (Pipe.comp s10
          (Pipe.comp s11 s12))))))))))
      refine Pipe.le h ?_
      simp only [c2]
      omega
    exact hchain rest
  -- the branching word
  have hIZ : WordR main (izComb q1 q2)
      (fun vs => vs = .int Fv :: ([.int Zv] ++ buCB p α s t ++ rest))
      (fun _ out => (Fv = 0 → out = [.int 0] ++ buCB p α s t ++ rest) ∧
        (Fv ≠ 0 → out = [.int (Int.tdiv Yv Dv)] ++ buCB p α s t ++ rest))
      (fun _ => Kiz * (isz Fv + 1) + max c1 c2) :=
    hiz main q1 q2 Fv ([.int Zv] ++ buCB p α s t ++ rest)
      (fun out => out = [.int 0] ++ buCB p α s t ++ rest)
      (fun out => out = [.int (Int.tdiv Yv Dv)] ++ buCB p α s t ++ rest) c1 c2 hQ1 hQ2
  -- assemble
  intro vs hvs st R hR
  obtain ⟨mid, st₁, n₁, hmid, hev₁, hn₁, hstk₁, hoth₁⟩ := hstepAB rest vs hvs st R hR
  have hpre : mid = .int Fv :: ([.int Zv] ++ buCB p α s t ++ rest) := by rw [hmid]; rfl
  obtain ⟨out, st₂, n₂, hpost, hev₂, hn₂, hstk₂, hoth₂⟩ := hIZ mid hpre st₁ R hstk₁
  have hcbpw : cb ≤ (Λ * 1000000 ^ 2) * (p + 1) ^ 4 := buSBW_le_pow p Λ
  have hizb : Kiz * (isz Fv + 1) ≤ cb := le_buSBW_one hΛiz hzF
  have hcs : n₁ + n₂ ≤ (14 * Λ * 1000000 ^ 2) * (p + 1) ^ 4 +
      (KZ * (p + 1) ^ KZ + (KF * (p + 1) ^ KF + Kh * (p + 1) ^ Kh)) :=
    buCostArith (p := p) (Λ := Λ) (KZ := KZ) (KF := KF) (Kh := Kh) (Kiz := Kiz)
      (cb := cb) (iszF := isz Fv) hn₁ hn₂ hizb hcbpw
  refine ⟨out, st₂, n₁ + n₂, ⟨hvs, ?_⟩, Eval.seq hev₁ hev₂, ?_, hstk₂, ?_⟩
  · -- the output value
    rcases hpost with ⟨hq1, hq2⟩
    by_cases hF0 : Fv = 0
    · rw [hq1 hF0]
      have hlt : auBnd p < Zv := (auFlgV_eq_zero_iff (p := p) (Z := Zv)).mp hF0
      have hng : ¬ (buZ p α s t ℓ h ≤ ((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ auPrec p) := by
        rw [← auBnd_eq p]
        exact not_le.mpr hlt
      rw [buWt_of_not_le p α s t ℓ h hng]
    · rw [hq2 hF0]
      have hge : Zv ≤ auBnd p := (auFlgV_ne_zero_iff (p := p) (Z := Zv)).mp hF0
      have hle : buZ p α s t ℓ h ≤ ((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ auPrec p := by
        rw [← auBnd_eq p]
        exact hge
      rw [buWt_of_le p α s t ℓ h hle]
      have hYv : Yv = auH p (-(buZ p α s t ℓ h)) (auNstep p) := rfl
      have hDv : Dv = (2 : ℤ) ^ (auPrec p - p) := by
        simp only [Dv]
        rw [auPrec_sub_self]
      rw [hYv, hDv]
  · exact le_trans hcs (buCostSum4 (14 * Λ * 1000000 ^ 2) 4 KZ KZ KF KF Kh Kh p)
  · intro k hk
    rw [hoth₂ k hk, hoth₁ k hk]

end Work.Resample
