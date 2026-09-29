import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buWtKit
import Submission.Work.Resample.buHornerKit
import Submission.Work.Resample.auPreKit

/-!
# `Work.Resample.buNFromParams`: the word computing `egN p α s t` from the four parameters

The one-dimensional `B̃` resampling (paper §4) works with the Neumann truncation length

`n = egN p α s t = (p·s - 1) / (α²·(t - s)) + 1`   (`Work.Resample.sliceB1defs`).

This module builds a word that turns the four integer values `[p, α, s, t]` into
`[egN p α s t, p, α, s, t]` (the result pushed on top of the preserved parameters) at cost
`K·(p+1)^K`, for `100 ≤ p`, `2 ≤ α`, `2 ≤ s < t < 2^p` and `α² < p`.

The word is the straight-line chain of `KernelLib`/`IntLib` primitives

`pick 2 ; pick 4 ; sub ; pick 2 ; pick 3 ; mulS ; mulS ; push 1 ; pick 4 ; pick 3 ;
 mulS ; sub ; fdiv ; push 1 ; add`,

i.e.  `t - s`, `α²`, `α²(t-s)`, then `1`, `p·s`, `p·s - 1`, the floor division and `+1`.
Every intermediate value has `isz ≤ buSZ p`, so every step costs at most `buSBW p Λ`; the
fifteen steps are absorbed into a single `K (p+1)^K` (`buN_cost15`, `buSBW_le_pow`, `le_powK`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## The value computed -/

/-- The computed floor quotient, plus one, is `egN`. -/
theorem buN_fdiv_cast (p α s t : ℕ) :
    Int.fdiv (((p * s - 1 : ℕ) : ℤ)) (((α ^ 2 * (t - s) : ℕ) : ℤ)) + 1
      = ((egN p α s t : ℕ) : ℤ) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by positivity : (0 : ℤ) ≤ ((α ^ 2 * (t - s) : ℕ) : ℤ))]
  rw [← Int.natCast_div (p * s - 1) (α ^ 2 * (t - s))]
  rw [egN, Nat.cast_add, Nat.cast_one]

/-! ## Size bounds for the intermediate values -/

theorem buN_isz_alpha (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) : isz ((α : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_pow_p ?_
  rw [Int.natAbs_natCast]
  have h1 : α ≤ α ^ 2 := by
    calc α = α * 1 := (Nat.mul_one α).symm
      _ ≤ α * α := Nat.mul_le_mul_left α (by omega)
      _ = α ^ 2 := (pow_two α).symm
  exact le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt h1 hαp) (le_of_lt (Nat.lt_two_pow_self (n := p))))

theorem buN_isz_ts (p s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) :
    isz (((t - s : ℕ) : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_pow_p ?_
  rw [Int.natAbs_natCast]
  exact le_trans (Nat.sub_le t s) (le_of_lt htp)

theorem buN_isz_alpha_sq (p α : ℕ) (hαp : α ^ 2 < p) : isz (((α ^ 2 : ℕ) : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_pow_p ?_
  rw [Int.natAbs_natCast]
  exact le_of_lt (lt_of_lt_of_le hαp (le_of_lt (Nat.lt_two_pow_self (n := p))))

theorem buN_isz_D (p α s t : ℕ) (hαp : α ^ 2 < p) (hst : s < t) (htp : t < 2 ^ p) :
    isz (((α ^ 2 * (t - s) : ℕ) : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_pow_2p ?_
  rw [Int.natAbs_natCast]
  calc α ^ 2 * (t - s) ≤ 2 ^ p * 2 ^ p :=
        Nat.mul_le_mul (le_of_lt (lt_of_lt_of_le hαp (le_of_lt (Nat.lt_two_pow_self (n := p)))))
          (le_trans (Nat.sub_le t s) (le_of_lt htp))
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf

theorem buN_isz_ps (p s : ℕ) (hsp : s < 2 ^ p) : isz (((p * s : ℕ) : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_pow_2p ?_
  rw [Int.natAbs_natCast]
  calc p * s ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt (Nat.lt_two_pow_self (n := p))) (le_of_lt hsp)
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf

theorem buN_isz_ps_sub (p s : ℕ) (hsp : s < 2 ^ p) : isz (((p * s - 1 : ℕ) : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_pow_2p ?_
  rw [Int.natAbs_natCast]
  refine le_trans (Nat.sub_le (p * s) 1) ?_
  calc p * s ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt (Nat.lt_two_pow_self (n := p))) (le_of_lt hsp)
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf

theorem buN_fdiv_int_eq (p α s t : ℕ) :
    Int.fdiv (((p * s - 1 : ℕ) : ℤ)) (((α ^ 2 * (t - s) : ℕ) : ℤ))
      = (((p * s - 1) / (α ^ 2 * (t - s)) : ℕ) : ℤ) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by positivity : (0 : ℤ) ≤ ((α ^ 2 * (t - s) : ℕ) : ℤ))]
  exact (Int.natCast_div (p * s - 1) (α ^ 2 * (t - s))).symm

theorem buN_isz_ff (p α s t : ℕ) (hsp : s < 2 ^ p) :
    isz (Int.fdiv (((p * s - 1 : ℕ) : ℤ)) (((α ^ 2 * (t - s) : ℕ) : ℤ))) ≤ buSZ p := by
  refine isz_le_buSZ_pow_2p ?_
  rw [buN_fdiv_int_eq, Int.natAbs_natCast]
  refine le_trans (Nat.div_le_self _ _) ?_
  calc p * s - 1 ≤ p * s := Nat.sub_le _ _
    _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt (Nat.lt_two_pow_self (n := p))) (le_of_lt hsp)
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf

/-! ## Cost absorption -/

/-- The right-nested sum of fifteen equal terms is at most `15 b`. -/
theorem buN_cost15 (b : ℕ) :
    (b + (b + (b + (b + (b + (b + (b + (b + (b + (b + (b + (b + (b + (b + b))))))))))))))
      ≤ 15 * b := by omega

/-! ## The word -/

theorem buNFromParams (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Work.Resample.Pipe main prog
        [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)]
        ([HvdH.Val.int ((Work.Resample.egN p α s t : ℕ) : ℤ)] ++
          [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)])
        (K * (p + 1) ^ K) := by
  obtain ⟨pickP, Kpick, hpick⟩ := KL.pick
  obtain ⟨pushProg, Kpush, hpush⟩ := KL.pushVal
  obtain ⟨subProg, Ksub, hsub⟩ := IL.sub
  obtain ⟨addProg, Kadd, hadd⟩ := IL.add
  obtain ⟨mulProg, Kmul, hmul⟩ := IL.mulS
  obtain ⟨fdivProg, Kfdiv, hfdiv⟩ := IL.fdiv
  let Λ : ℕ := Kpick + Kpush + Ksub + Kadd + Kmul + Kfdiv + 1
  let K : ℕ := 8 * ((15 * (Λ * 1000000 ^ 2) + 1) + 4) + 8
  let prog : Cmd := Cmd.seq (pickP 2) (Cmd.seq (pickP 4) (Cmd.seq subProg (Cmd.seq (pickP 2)
    (Cmd.seq (pickP 3) (Cmd.seq mulProg (Cmd.seq mulProg (Cmd.seq (pushProg (.int 1))
    (Cmd.seq (pickP 4) (Cmd.seq (pickP 3) (Cmd.seq mulProg (Cmd.seq subProg (Cmd.seq fdivProg
    (Cmd.seq (pushProg (.int 1)) addProg)))))))))))))
  refine ⟨prog, K, ?_⟩
  intro main p α s t hs hst hα hp htp hαp
  let ts : ℤ := ((t - s : ℕ) : ℤ)
  let a2 : ℤ := ((α ^ 2 : ℕ) : ℤ)
  let DD : ℤ := ((α ^ 2 * (t - s) : ℕ) : ℤ)
  let ps : ℤ := ((p * s : ℕ) : ℤ)
  let YY : ℤ := ((p * s - 1 : ℕ) : ℤ)
  let ff : ℤ := Int.fdiv YY DD
  have hsp : s < 2 ^ p := lt_trans hst htp
  -- ## size bounds
  have hpZ : isz ((p : ℤ)) ≤ buSZ p :=
    isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact le_of_lt (Nat.lt_two_pow_self (n := p)))
  have hαZ : isz ((α : ℤ)) ≤ buSZ p := buN_isz_alpha p α hα hαp
  have hsZ : isz ((s : ℤ)) ≤ buSZ p :=
    isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact le_of_lt hsp)
  have htZ : isz ((t : ℤ)) ≤ buSZ p :=
    isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact le_of_lt htp)
  have htsZ : isz ts ≤ buSZ p := buN_isz_ts p s t hst htp
  have ha2Z : isz a2 ≤ buSZ p := buN_isz_alpha_sq p α hαp
  have hDDZ : isz DD ≤ buSZ p := buN_isz_D p α s t hαp hst htp
  have h1Z : isz ((1 : ℤ)) ≤ buSZ p := isz_const_le_buSZ p 1 (by omega)
  have hpsZ : isz ps ≤ buSZ p := buN_isz_ps p s hsp
  have hYYZ : isz YY ≤ buSZ p := buN_isz_ps_sub p s hsp
  have hffZ : isz ff ≤ buSZ p := buN_isz_ff p α s t hsp
  have hv1Z : vsz (.int (1 : ℤ)) ≤ buSZ p := vsz_int_le_buSZ h1Z
  -- ## the constants
  have hΛpick : Kpick ≤ Λ := by simp only [Λ]; omega
  have hΛpush : Kpush ≤ Λ := by simp only [Λ]; omega
  have hΛsub : Ksub ≤ Λ := by simp only [Λ]; omega
  have hΛadd : Kadd ≤ Λ := by simp only [Λ]; omega
  have hΛmul : Kmul ≤ Λ := by simp only [Λ]; omega
  have hΛfdiv : Kfdiv ≤ Λ := by simp only [Λ]; omega
  -- ## the positive divisor
  have hDpos : (0 : ℤ) < DD := by
    have h1 : 0 < α ^ 2 := pow_pos (by omega : (0:ℕ) < α) 2
    have h2 : 0 < t - s := Nat.sub_pos_of_lt hst
    have h3 : 0 < α ^ 2 * (t - s) := Nat.mul_pos h1 h2
    have h3' : (0 : ℤ) < ((α ^ 2 * (t - s) : ℕ) : ℤ) := by exact_mod_cast h3
    exact h3'
  have hp1s : 1 ≤ p * s := by
    have := Nat.mul_le_mul hp hs
    omega
  -- ## the fifteen steps
  have s1 : Pipe main (pickP 2)
      [.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int (s : ℤ), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)] (buSBW p Λ) := by
    refine Pipe.le (Pipe.pickAt main hpick
      (A := [.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]) (k := 2) (by simp)
      (v := .int (s : ℤ)) (by simp))
      (le_buSBW_roll hΛpick (by norm_num) (by simp)
        (vsz_mem_le_cons (vsz_int_le_buSZ hpZ) (vsz_mem_le_cons (vsz_int_le_buSZ hαZ)
          (vsz_mem_le_cons (vsz_int_le_buSZ hsZ) (vsz_mem_le_cons (vsz_int_le_buSZ htZ)
            vsz_mem_le_nil)))))
  have s2 : Pipe main (pickP 4)
      [.int (s : ℤ), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int (t : ℤ), .int (s : ℤ), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (buSBW p Λ) := by
    refine Pipe.le (Pipe.pickAt main hpick
      (A := [.int (s : ℤ), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]) (k := 4)
      (by simp) (v := .int (t : ℤ)) (by simp))
      (le_buSBW_roll hΛpick (by norm_num) (by simp)
        (vsz_mem_le_cons (vsz_int_le_buSZ hsZ) (vsz_mem_le_cons (vsz_int_le_buSZ hpZ)
          (vsz_mem_le_cons (vsz_int_le_buSZ hαZ) (vsz_mem_le_cons (vsz_int_le_buSZ hsZ)
            (vsz_mem_le_cons (vsz_int_le_buSZ htZ) vsz_mem_le_nil))))))
  have s3 : Pipe main subProg
      [.int (t : ℤ), .int (s : ℤ), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)] (buSBW p Λ) := by
    have h0 : Pipe main subProg [.int (t : ℤ), .int (s : ℤ)] [.int ((t : ℤ) - (s : ℤ))]
        (Ksub * (isz (t : ℤ) + isz (s : ℤ))) :=
      Pipe.binOp (hsub main) (a := (t : ℤ)) (b := (s : ℤ)) trivial
    have h1 := Pipe.appendTail ([.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]) h0
    refine Pipe.le (Pipe.rw h1 ?_) (le_buSBW_two hΛsub htZ hsZ)
    rw [show (t : ℤ) - (s : ℤ) = ts from (Nat.cast_sub (le_of_lt hst)).symm]
    rfl
  have s4 : Pipe main (pickP 2)
      [.int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int (α : ℤ), .int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (buSBW p Λ) := by
    refine Pipe.le (Pipe.pickAt main hpick
      (A := [.int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]) (k := 2) (by simp)
      (v := .int (α : ℤ)) (by simp))
      (le_buSBW_roll hΛpick (by norm_num) (by simp)
        (vsz_mem_le_cons (vsz_int_le_buSZ htsZ) (vsz_mem_le_cons (vsz_int_le_buSZ hpZ)
          (vsz_mem_le_cons (vsz_int_le_buSZ hαZ) (vsz_mem_le_cons (vsz_int_le_buSZ hsZ)
            (vsz_mem_le_cons (vsz_int_le_buSZ htZ) vsz_mem_le_nil))))))
  have s5 : Pipe main (pickP 3)
      [.int (α : ℤ), .int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int (α : ℤ), .int (α : ℤ), .int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (buSBW p Λ) := by
    refine Pipe.le (Pipe.pickAt main hpick
      (A := [.int (α : ℤ), .int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)])
      (k := 3) (by simp) (v := .int (α : ℤ)) (by simp))
      (le_buSBW_roll hΛpick (by norm_num) (by simp)
        (vsz_mem_le_cons (vsz_int_le_buSZ hαZ) (vsz_mem_le_cons (vsz_int_le_buSZ htsZ)
          (vsz_mem_le_cons (vsz_int_le_buSZ hpZ) (vsz_mem_le_cons (vsz_int_le_buSZ hαZ)
            (vsz_mem_le_cons (vsz_int_le_buSZ hsZ) (vsz_mem_le_cons (vsz_int_le_buSZ htZ)
              vsz_mem_le_nil)))))))
  have s6 : Pipe main mulProg
      [.int (α : ℤ), .int (α : ℤ), .int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int a2, .int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)] (buSBW p Λ) := by
    have h0 : Pipe main mulProg [.int (α : ℤ), .int (α : ℤ)] [.int ((α : ℤ) * (α : ℤ))]
        (Kmul * isz (α : ℤ) * isz (α : ℤ)) :=
      Pipe.binOp (hmul main) (a := (α : ℤ)) (b := (α : ℤ)) trivial
    have h1 := Pipe.appendTail ([.int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]) h0
    refine Pipe.le (Pipe.rw h1 ?_) (le_buSBW_mul hΛmul hαZ hαZ)
    have ha2eq : (α : ℤ) * (α : ℤ) = a2 := by
      have e : a2 = ((α ^ 2 : ℕ) : ℤ) := rfl
      rw [e]; push_cast; ring
    rw [ha2eq]
    rfl
  have s7 : Pipe main mulProg
      [.int a2, .int ts, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)] (buSBW p Λ) := by
    have h0 : Pipe main mulProg [.int a2, .int ts] [.int (a2 * ts)] (Kmul * isz a2 * isz ts) :=
      Pipe.binOp (hmul main) (a := a2) (b := ts) trivial
    have h1 := Pipe.appendTail ([.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]) h0
    refine Pipe.le (Pipe.rw h1 ?_) (le_buSBW_mul hΛmul ha2Z htsZ)
    have hDD : a2 * ts = DD := by
      have e1 : a2 = ((α ^ 2 : ℕ) : ℤ) := rfl
      have e2 : ts = ((t - s : ℕ) : ℤ) := rfl
      have e3 : DD = ((α ^ 2 * (t - s) : ℕ) : ℤ) := rfl
      rw [e1, e2, e3]
      exact (Nat.cast_mul (α ^ 2) (t - s)).symm
    rw [hDD]
    rfl
  have s8 : Pipe main (pushProg (.int 1))
      [.int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (buSBW p Λ) := by
    refine Pipe.le (Pipe.pushOnAny (T := [.int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ),
      .int (t : ℤ)]) (hpush main (.int 1))) (le_buSBW_one hΛpush hv1Z)
  have s9 : Pipe main (pickP 4)
      [.int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int (s : ℤ), .int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (buSBW p Λ) := by
    refine Pipe.le (Pipe.pickAt main hpick
      (A := [.int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)])
      (k := 4) (by simp) (v := .int (s : ℤ)) (by simp))
      (le_buSBW_roll hΛpick (by norm_num) (by simp)
        (vsz_mem_le_cons (vsz_int_le_buSZ h1Z) (vsz_mem_le_cons (vsz_int_le_buSZ hDDZ)
          (vsz_mem_le_cons (vsz_int_le_buSZ hpZ) (vsz_mem_le_cons (vsz_int_le_buSZ hαZ)
            (vsz_mem_le_cons (vsz_int_le_buSZ hsZ) (vsz_mem_le_cons (vsz_int_le_buSZ htZ)
              vsz_mem_le_nil)))))))
  have s10 : Pipe main (pickP 3)
      [.int (s : ℤ), .int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int (p : ℤ), .int (s : ℤ), .int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ),
        .int (t : ℤ)] (buSBW p Λ) := by
    refine Pipe.le (Pipe.pickAt main hpick
      (A := [.int (s : ℤ), .int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ),
        .int (t : ℤ)]) (k := 3) (by simp) (v := .int (p : ℤ)) (by simp))
      (le_buSBW_roll hΛpick (by norm_num) (by simp)
        (vsz_mem_le_cons (vsz_int_le_buSZ hsZ) (vsz_mem_le_cons (vsz_int_le_buSZ h1Z)
          (vsz_mem_le_cons (vsz_int_le_buSZ hDDZ) (vsz_mem_le_cons (vsz_int_le_buSZ hpZ)
            (vsz_mem_le_cons (vsz_int_le_buSZ hαZ) (vsz_mem_le_cons (vsz_int_le_buSZ hsZ)
              (vsz_mem_le_cons (vsz_int_le_buSZ htZ) vsz_mem_le_nil))))))))
  have s11 : Pipe main mulProg
      [.int (p : ℤ), .int (s : ℤ), .int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ),
        .int (s : ℤ), .int (t : ℤ)]
      [.int ps, .int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (buSBW p Λ) := by
    have h0 : Pipe main mulProg [.int (p : ℤ), .int (s : ℤ)] [.int ((p : ℤ) * (s : ℤ))]
        (Kmul * isz (p : ℤ) * isz (s : ℤ)) :=
      Pipe.binOp (hmul main) (a := (p : ℤ)) (b := (s : ℤ)) trivial
    have h1 := Pipe.appendTail ([.int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ),
      .int (s : ℤ), .int (t : ℤ)]) h0
    refine Pipe.le (Pipe.rw h1 ?_) (le_buSBW_mul hΛmul hpZ hsZ)
    have hpseq : (p : ℤ) * (s : ℤ) = ps := by
      have e : ps = ((p * s : ℕ) : ℤ) := rfl
      rw [e]
      exact (Nat.cast_mul p s).symm
    rw [hpseq]
    rfl
  have s12 : Pipe main subProg
      [.int ps, .int (1 : ℤ), .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int YY, .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (buSBW p Λ) := by
    have h0 : Pipe main subProg [.int ps, .int (1 : ℤ)] [.int (ps - (1 : ℤ))]
        (Ksub * (isz ps + isz (1 : ℤ))) :=
      Pipe.binOp (hsub main) (a := ps) (b := (1 : ℤ)) trivial
    have h1 := Pipe.appendTail ([.int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]) h0
    refine Pipe.le (Pipe.rw h1 ?_) (le_buSBW_two hΛsub hpsZ h1Z)
    have hYYeq : ps - (1 : ℤ) = YY := by
      have e1 : ps = ((p * s : ℕ) : ℤ) := rfl
      have e2 : YY = ((p * s - 1 : ℕ) : ℤ) := rfl
      rw [e1, e2]
      exact (Nat.cast_sub hp1s).symm
    rw [hYYeq]
    rfl
  have s13 : Pipe main fdivProg
      [.int YY, .int DD, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int ff, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)] (buSBW p Λ) := by
    have h0 : Pipe main fdivProg [.int YY, .int DD] [.int (Int.fdiv YY DD)]
        (Kfdiv * isz YY * isz DD) :=
      Pipe.binOp (hfdiv main) (a := YY) (b := DD) hDpos
    have h1 := Pipe.appendTail ([.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]) h0
    refine Pipe.le (Pipe.rw h1 ?_) (le_buSBW_mul hΛfdiv hYYZ hDDZ)
    rw [show Int.fdiv YY DD = ff from rfl]
    rfl
  have s14 : Pipe main (pushProg (.int 1))
      [.int ff, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int (1 : ℤ), .int ff, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (buSBW p Λ) := by
    refine Pipe.le (Pipe.pushOnAny (T := [.int ff, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ),
      .int (t : ℤ)]) (hpush main (.int 1))) (le_buSBW_one hΛpush hv1Z)
  have s15 : Pipe main addProg
      [.int (1 : ℤ), .int ff, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      [.int ((1 : ℤ) + ff), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (buSBW p Λ) := by
    have h0 : Pipe main addProg [.int (1 : ℤ), .int ff] [.int ((1 : ℤ) + ff)]
        (Kadd * (isz (1 : ℤ) + isz ff)) :=
      Pipe.binOp (hadd main) (a := (1 : ℤ)) (b := ff) trivial
    exact Pipe.le (Pipe.appendTail ([.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]) h0)
      (le_buSBW_two hΛadd h1Z hffZ)
  -- ## assembly
  have hchain := Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5
    (Pipe.comp s6 (Pipe.comp s7 (Pipe.comp s8 (Pipe.comp s9 (Pipe.comp s10 (Pipe.comp s11
    (Pipe.comp s12 (Pipe.comp s13 (Pipe.comp s14 s15)))))))))))))
  have hval : (1 : ℤ) + ff = ((egN p α s t : ℕ) : ℤ) := by
    have e : ff = Int.fdiv (((p * s - 1 : ℕ) : ℤ)) (((α ^ 2 * (t - s) : ℕ) : ℤ)) := rfl
    rw [e, add_comm]
    exact buN_fdiv_cast p α s t
  have hb : buSBW p Λ ≤ (Λ * 1000000 ^ 2) * (p + 1) ^ 4 := buSBW_le_pow p Λ
  have hK15 : 15 * ((Λ * 1000000 ^ 2) * (p + 1) ^ 4) ≤ K * (p + 1) ^ K := by
    have h1 : 15 * ((Λ * 1000000 ^ 2) * (p + 1) ^ 4)
        = (15 * (Λ * 1000000 ^ 2)) * (p + 1) ^ 4 := by ring
    rw [h1]
    have hpK := le_powK (p := p) (c := 15 * (Λ * 1000000 ^ 2) + 1) (d := 4)
      (by omega) (by omega)
    refine le_trans (Nat.mul_le_mul_right _ (Nat.le_succ _)) ?_
    simpa only [K] using hpK
  refine Pipe.le (Pipe.rw hchain ?_) (le_trans (buN_cost15 (buSBW p Λ)) ?_)
  · rw [hval, List.cons_append, List.nil_append]
    try rfl
  · calc 15 * buSBW p Λ ≤ 15 * ((Λ * 1000000 ^ 2) * (p + 1) ^ 4) :=
        Nat.mul_le_mul_left _ hb
      _ ≤ K * (p + 1) ^ K := hK15

end Work.Resample
