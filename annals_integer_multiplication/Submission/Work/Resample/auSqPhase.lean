import Mathlib
import Submission.Work.Resample.auKit

/-!
# `Work.Resample.auSqPhase`

The word computing the *quadratic phase* value `(C + t·i)²` from the loop index `i`, keeping the
rest of the parameter window `[i, auPi p, C, t, p, α]` in place:

`[i, auPi p, C, t, p, α] ↦ [(C + t·i)², auPi p, C, t, p, α]`.

The word is a chain of eight library calls:
`pick 3` (copy `t`), `swap`, `mulS` (get `t·i`), `pick 2` (copy `C`), `swap`, `add`
(get `t·i + C`), `dup`, `mulS` (square).
-/

set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH

/-! ## A power-sandwich -/

/-- Absorbing a constant into the exponent.  For `1 ≤ M` and `2 ≤ p+1`,
`M (p+1)^2 ≤ (8M+6) (p+1)^(8M+6)`. -/
theorem pow_bound_auSq {M p : ℕ} (hM : 1 ≤ M) (hp : 2 ≤ p + 1) :
    M * (p + 1) ^ 2 ≤ (8 * M + 6) * (p + 1) ^ (8 * M + 6) := by
  have h1 : M < 2 ^ (4 * M + 3) :=
    lt_of_le_of_lt (show M ≤ 4 * M + 3 by omega) (Nat.lt_two_pow_self (n := 4 * M + 3))
  have h2 : (2 : ℕ) ^ (4 * M + 3) ≤ (p + 1) ^ (4 * M + 3) := Nat.pow_le_pow_left hp _
  have hMle : M ≤ (p + 1) ^ (4 * M + 3) := le_of_lt (lt_of_lt_of_le h1 h2)
  have hbase : 1 ≤ p + 1 := by omega
  have h3 : (p + 1) ^ 2 ≤ (p + 1) ^ (4 * M + 3) := Nat.pow_le_pow_right hbase (by omega)
  have h4 : M * (p + 1) ^ 2 ≤ (p + 1) ^ (4 * M + 3) * (p + 1) ^ (4 * M + 3) :=
    Nat.mul_le_mul hMle h3
  have h5 : (p + 1) ^ (4 * M + 3) * (p + 1) ^ (4 * M + 3) = (p + 1) ^ (8 * M + 6) := by
    rw [← pow_add]; congr 1; ring
  have h6 : (p + 1) ^ (8 * M + 6) ≤ (8 * M + 6) * (p + 1) ^ (8 * M + 6) := by
    simpa using Nat.mul_le_mul_right ((p + 1) ^ (8 * M + 6)) (show 1 ≤ 8 * M + 6 by omega)
  calc M * (p + 1) ^ 2
      ≤ (p + 1) ^ (4 * M + 3) * (p + 1) ^ (4 * M + 3) := h4
    _ = (p + 1) ^ (8 * M + 6) := h5
    _ ≤ (8 * M + 6) * (p + 1) ^ (8 * M + 6) := h6

/-! ## `szl` of a literal list of integer values -/

theorem szl_int4 (a b c d : ℤ) :
    Work.Fx.szl [Val.int a, Val.int b, Val.int c, Val.int d] = isz a + isz b + isz c + isz d := by
  simp [Work.Fx.szl, Work.Fx.vsz_int]
  ring

/-! ## The word -/

theorem auSqPhase (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α t : ℕ) (C i : ℤ),
      (1 ≤ p) →
      HvdH.isz i ≤ Work.Resample.auSZ p → HvdH.isz C ≤ Work.Resample.auSZ p →
      HvdH.isz ((t : ℤ)) ≤ Work.Resample.auSZ p → HvdH.isz ((p : ℤ)) ≤ Work.Resample.auSZ p →
      HvdH.isz ((α : ℤ)) ≤ Work.Resample.auSZ p →
      HvdH.isz (Work.Resample.auPi p) ≤ Work.Resample.auSZ p →
      Work.Resample.Pipe main prog
        [HvdH.Val.int i, HvdH.Val.int (Work.Resample.auPi p), HvdH.Val.int C,
          HvdH.Val.int (t : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        [HvdH.Val.int ((C + (t : ℤ) * i) ^ 2), HvdH.Val.int (Work.Resample.auPi p), HvdH.Val.int C,
          HvdH.Val.int (t : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        (K * (p + 1) ^ K) := by
  obtain ⟨pickProg, Kpk, hpick⟩ := hk.pick
  obtain ⟨swapProg, Ks, hswap⟩ := hk.swap
  obtain ⟨dupProg, Kd, hdup⟩ := hk.dup
  obtain ⟨mulProg, Km, hmul⟩ := hi.mulS
  obtain ⟨addProg, Kc, hadd⟩ := hi.add
  let Λ : ℕ := Kpk + Ks + Km + Kc + Kd + 1
  let M : ℕ := 8 * Λ * 3208 ^ 2
  let K : ℕ := 8 * M + 6
  let prog : HvdH.Cmd :=
    HvdH.Cmd.seq (pickProg 3)
      (HvdH.Cmd.seq swapProg
        (HvdH.Cmd.seq mulProg
          (HvdH.Cmd.seq (pickProg 2)
            (HvdH.Cmd.seq swapProg
              (HvdH.Cmd.seq addProg
                (HvdH.Cmd.seq dupProg mulProg))))))
  refine ⟨prog, K, ?_⟩
  intro main p α t C i hp1 hzi hzC hzt hzp hzα hzpi
  -- size facts
  have hS : 400 ≤ auSZ p := auSZ_ge p
  have hzpil : isz (auPi p) ≤ auSZ p := isz_auPi_le p
  have hzti : isz (i * (t : ℤ)) ≤ 2 * auSZ p := by
    have h := Work.Fx.isz_mul_le i (t : ℤ); omega
  have hzx : isz (i * (t : ℤ) + C) ≤ 2 * auSZ p + 1 := by
    have h := Work.Fx.isz_add_le (i * (t : ℤ)) C
    have h2 : max (isz (i * (t : ℤ))) (isz C) ≤ 2 * auSZ p := max_le hzti (by omega)
    omega
  -- the value windows
  let T1 : List Val := [Val.int (auPi p), Val.int C, Val.int (t : ℤ), Val.int (p : ℤ),
    Val.int (α : ℤ)]
  let v0 : List Val := Val.int i :: T1
  let v1 : List Val := Val.int (t : ℤ) :: v0
  let v2 : List Val := Val.int i :: Val.int (t : ℤ) :: T1
  let v3 : List Val := Val.int (i * (t : ℤ)) :: T1
  let v4 : List Val := Val.int C :: Val.int (i * (t : ℤ)) :: T1
  let v5 : List Val := Val.int (i * (t : ℤ)) :: Val.int C :: T1
  let v6 : List Val := Val.int (i * (t : ℤ) + C) :: T1
  let v7 : List Val := Val.int (i * (t : ℤ) + C) :: Val.int (i * (t : ℤ) + C) :: T1
  let v8 : List Val := Val.int ((i * (t : ℤ) + C) * (i * (t : ℤ) + C)) :: T1
  -- the per-step cost bound
  let cb : ℕ := Λ * (8 * auSZ p + 8) ^ 2
  have hΛ1 : Kpk ≤ Λ := by simp only [Λ]; omega
  have hΛ2 : Ks ≤ Λ := by simp only [Λ]; omega
  have hΛ3 : Km ≤ Λ := by simp only [Λ]; omega
  have hΛ4 : Kc ≤ Λ := by simp only [Λ]; omega
  have hΛ5 : Kd ≤ Λ := by simp only [Λ]; omega
  have hcb : ∀ {Ki X : ℕ}, Ki ≤ Λ → X ≤ (8 * auSZ p + 8) ^ 2 → Ki * X ≤ cb := by
    intro Ki X hK hX
    simp only [cb]
    exact Nat.mul_le_mul hK hX
  -- `szl` bounds for the two windows on which `pick` is used
  have hszlv0 : Work.Fx.szl v0 ≤ 6 * auSZ p := by
    have h : Work.Fx.szl v0 = isz i + (isz (auPi p) + (isz C + (isz (t : ℤ) +
        (isz (p : ℤ) + isz (α : ℤ))))) := by
      simp [v0, T1, Work.Fx.szl, Work.Fx.vsz_int]
    omega
  have hszlv3 : Work.Fx.szl v3 ≤ 7 * auSZ p := by
    have h : Work.Fx.szl v3 = isz (i * (t : ℤ)) + (isz (auPi p) + (isz C + (isz (t : ℤ) +
        (isz (p : ℤ) + isz (α : ℤ))))) := by
      simp [v3, T1, Work.Fx.szl, Work.Fx.vsz_int]
    omega
  -- step 1: copy `t` to the top
  have s1 : Pipe main (pickProg 3) v0 v1 cb := by
    have hp := Pipe.pickAt (prog := pickProg) (K := Kpk) main hpick (A := v0) (k := 3)
      (v := Val.int (t : ℤ)) (by simp [v0, T1]) (by simp [v0, T1])
    refine Pipe.le hp ?_
    rw [Nat.mul_assoc]
    refine hcb hΛ1 ?_
    have hszl : Work.Fx.szl (v0.take (3 + 1)) ≤ 6 * auSZ p :=
      le_trans (szl_take_le v0 _) hszlv0
    nlinarith [hS, hszl]
  -- step 2: swap to bring `i` on top
  have s2 : Pipe main swapProg v1 v2 cb := by
    have hp := Pipe.appendTail T1 (Pipe.swap main hswap (Val.int (t : ℤ)) (Val.int i))
    refine Pipe.le hp ?_
    refine hcb hΛ2 ?_
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int]
    nlinarith [hS, hzt, hzi]
  -- step 3: `t · i`
  have s3 : Pipe main mulProg v2 v3 cb := by
    have hp := Pipe.appendTail T1 (Pipe.binOp (hmul main) (a := i) (b := (t : ℤ)) trivial)
    refine Pipe.le hp ?_
    rw [Nat.mul_assoc]
    refine hcb hΛ3 ?_
    nlinarith [hS, hzi, hzt]
  -- step 4: copy `C` to the top
  have s4 : Pipe main (pickProg 2) v3 v4 cb := by
    have hp := Pipe.pickAt (prog := pickProg) (K := Kpk) main hpick (A := v3) (k := 2)
      (v := Val.int C) (by simp [v3, T1]) (by simp [v3, T1])
    refine Pipe.le hp ?_
    rw [Nat.mul_assoc]
    refine hcb hΛ1 ?_
    have hszl : Work.Fx.szl (v3.take (2 + 1)) ≤ 7 * auSZ p :=
      le_trans (szl_take_le v3 _) hszlv3
    nlinarith [hS, hszl]
  -- step 5: swap to bring `t·i` on top
  have s5 : Pipe main swapProg v4 v5 cb := by
    have hp := Pipe.appendTail T1 (Pipe.swap main hswap (Val.int C) (Val.int (i * (t : ℤ))))
    refine Pipe.le hp ?_
    refine hcb hΛ2 ?_
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int]
    nlinarith [hS, hzti, hzC]
  -- step 6: `t·i + C`
  have s6 : Pipe main addProg v5 v6 cb := by
    have hp := Pipe.appendTail T1 (Pipe.binOp (hadd main) (a := i * (t : ℤ)) (b := C) trivial)
    refine Pipe.le hp ?_
    refine hcb hΛ4 ?_
    nlinarith [hS, hzti, hzC]
  -- step 7: duplicate
  have s7 : Pipe main dupProg v6 v7 cb := by
    have hp := Pipe.appendTail T1 (Pipe.dup main hdup (Val.int (i * (t : ℤ) + C)))
    refine Pipe.le hp ?_
    refine hcb hΛ5 ?_
    rw [Work.Fx.vsz_int]
    nlinarith [hS, hzx]
  -- step 8: square
  have s8 : Pipe main mulProg v7 v8 cb := by
    have hp := Pipe.appendTail T1
      (Pipe.binOp (hmul main) (a := i * (t : ℤ) + C) (b := i * (t : ℤ) + C) trivial)
    refine Pipe.le hp ?_
    rw [Nat.mul_assoc]
    refine hcb hΛ3 ?_
    nlinarith [hS, hzx]
  have hcomp : Pipe main prog v0 v8
      (cb + (cb + (cb + (cb + (cb + (cb + (cb + cb))))))) :=
    Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6
      (Pipe.comp s7 s8))))))
  have hM1 : 1 ≤ M := by
    have hΛ1' : 1 ≤ Λ := by simp only [Λ]; omega
    simp only [M]
    nlinarith [hΛ1']
  have hp2 : 2 ≤ p + 1 := by omega
  have hle : cb + (cb + (cb + (cb + (cb + (cb + (cb + cb)))))) ≤ K * (p + 1) ^ K := by
    have h1 : cb + (cb + (cb + (cb + (cb + (cb + (cb + cb)))))) ≤ 8 * cb := by omega
    have h2 : 8 * cb ≤ M * (p + 1) ^ 2 := by
      simp only [cb, M]
      have hSB : 8 * auSZ p + 8 ≤ 3208 * (p + 1) := by simp only [auSZ]; omega
      have hsq : (8 * auSZ p + 8) ^ 2 ≤ (3208 * (p + 1)) ^ 2 := Nat.pow_le_pow_left hSB 2
      have hsq2 : (3208 * (p + 1)) ^ 2 = 3208 ^ 2 * (p + 1) ^ 2 := by ring
      calc 8 * (Λ * (8 * auSZ p + 8) ^ 2)
          = 8 * Λ * (8 * auSZ p + 8) ^ 2 := by ring
        _ ≤ 8 * Λ * (3208 * (p + 1)) ^ 2 := Nat.mul_le_mul_left _ hsq
        _ = 8 * Λ * 3208 ^ 2 * (p + 1) ^ 2 := by rw [hsq2]; ring
    have h3 : M * (p + 1) ^ 2 ≤ K * (p + 1) ^ K := by
      simp only [K]
      exact pow_bound_auSq hM1 hp2
    exact le_trans h1 (le_trans h2 h3)
  have hB : v8 = [Val.int ((C + (t : ℤ) * i) ^ 2), Val.int (auPi p), Val.int C,
      Val.int (t : ℤ), Val.int (p : ℤ), Val.int (α : ℤ)] := by
    show Val.int ((i * (t : ℤ) + C) * (i * (t : ℤ) + C)) :: T1
        = Val.int ((C + (t : ℤ) * i) ^ 2) :: T1
    rw [show (i * (t : ℤ) + C) * (i * (t : ℤ) + C) = (C + (t : ℤ) * i) ^ 2 from by ring]
  exact Pipe.rw (Pipe.le hcomp hle) hB

end Work.Resample
