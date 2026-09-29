import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buWdKit
import Submission.Work.Resample.buDivDefs
import Submission.Work.Resample.buDivStepA
import Submission.Work.Resample.buDivStepC
import Submission.Work.Resample.buDivStepD

set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-! ## Elementary arithmetic bounds -/

theorem buDivB_mul_le_sq {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) : a * b ≤ n ^ 2 := by
  calc a * b ≤ n * b := Nat.mul_le_mul_right b ha
    _ ≤ n * n := Nat.mul_le_mul_left n hb
    _ = n ^ 2 := by ring

theorem buDivB_add_le_sq {n a b : ℕ} (hn : 2 ≤ n) (ha : a ≤ n) (hb : b ≤ n) : a + b ≤ n ^ 2 := by
  calc a + b ≤ n + n := Nat.add_le_add ha hb
    _ ≤ n * n := by nlinarith
    _ = n ^ 2 := by ring

theorem buDivB_succ_le_sq {n a : ℕ} (hn : 2 ≤ n) (ha : a ≤ n) : a + 1 ≤ n ^ 2 := by
  calc a + 1 ≤ n + 1 := by omega
    _ ≤ n * n := by nlinarith
    _ = n ^ 2 := by ring

theorem add_buDivB_succ_le_sq {n a b : ℕ} (hn : 3 ≤ n) (ha : a ≤ n) (hb : b ≤ n) :
    a + b + 1 ≤ n ^ 2 := by
  calc a + b + 1 ≤ n + n + 1 := by omega
    _ ≤ n * n := by nlinarith
    _ = n ^ 2 := by ring

/-- Six equal steps are within eight of them. -/
theorem buDivB_six_le_eight (m n : ℕ) :
    m * n ^ 2 + m * n ^ 2 + m * n ^ 2 + m * n ^ 2 + m * n ^ 2 + m * n ^ 2 ≤ 8 * m * n ^ 2 := by
  nlinarith [Nat.zero_le (m * n ^ 2)]

/-! ## Size bounds for the values of the window -/

theorem buDivB_isz_cast_le_buSZ_of {p n B : ℕ} (hn : n < 2 ^ B) (hB : B + 2 ≤ buSZ p + 8) :
    isz ((n : ℤ)) ≤ buSZ p + 8 := by
  have h1 : n.size ≤ B := Nat.size_le.mpr hn
  have h2 : isz ((n : ℤ)) = n.size + 2 := by simp only [isz, Int.natAbs_natCast]
  rw [h2]; omega

theorem buDivB_isz_alpha_le (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) :
    isz ((α : ℤ)) ≤ buSZ p + 8 := by
  refine buDivB_isz_cast_le_buSZ_of (B := p) ?_ ?_
  · calc α < p := by nlinarith
      _ < 2 ^ p := Nat.lt_two_pow_self
  · simp only [buSZ]; omega

theorem buDivB_isz_buDivZ1_le (p α : ℕ) (hαp : α ^ 2 < p) : isz (buDivZ1 α) ≤ buSZ p + 8 := by
  have h2 : buDivZ1 α = ((α * α : ℕ) : ℤ) := by simp only [buDivZ1]; push_cast; ring
  rw [h2]
  refine buDivB_isz_cast_le_buSZ_of (B := p) ?_ ?_
  · calc α * α < p := by nlinarith
      _ < 2 ^ p := Nat.lt_two_pow_self
  · simp only [buSZ]; omega

theorem buDivB_isz_buDivZ2_le (p α : ℕ) (hαp : α ^ 2 < p) : isz (buDivZ2 α) ≤ buSZ p + 8 := by
  have h2 : buDivZ2 α = ((2 * (α * α) : ℕ) : ℤ) := by
    simp only [buDivZ2, buDivZ1]; push_cast; ring
  rw [h2]
  refine buDivB_isz_cast_le_buSZ_of (B := p + 1) ?_ ?_
  · have h4 : α * α < 2 ^ p := by
      calc α * α < p := by nlinarith
        _ < 2 ^ p := Nat.lt_two_pow_self
    calc 2 * (α * α) < 2 * 2 ^ p := by omega
      _ = 2 ^ (p + 1) := by ring
  · simp only [buSZ]; omega

/-! ## The step -/

private theorem buDivB (KL : HvdH.KernelLib) (IL : HvdH.IntLib) : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) (Ad : ℤ) (hAd : HvdH.isz Ad ≤ Work.Resample.buSZ p) (V : List HvdH.Val), Work.Resample.Pipe main prog ([HvdH.Val.int (α : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int Ad, HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)] ++ V) ([HvdH.Val.int (Work.Resample.buDivZ3 α), HvdH.Val.int Ad, HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)] ++ V) (K * (Work.Resample.buSZ p + 8) ^ 2) := by
  obtain ⟨gms, Kms, hms⟩ := IL.mulS
  obtain ⟨gdup, Kd, hdup⟩ := KL.dup
  obtain ⟨gadd, Kad, hadd⟩ := IL.add
  obtain ⟨gpv, Kpv, hpv⟩ := KL.pushVal
  obtain ⟨gsw, Ksw, hsw⟩ := KL.swap
  obtain ⟨gsub, Ksu, hsub⟩ := IL.sub
  refine ⟨((((gms ;;; gdup) ;;; gadd) ;;; gpv (Val.int 2)) ;;; gsw) ;;; gsub,
    8 * (Kms + Kd + Kad + Kpv + Ksw + Ksu + 1), ?_⟩
  intro main p α hα hαp Ad hAd V
  have hn : 2 ≤ buSZ p + 8 := by have := buSZ_ge p; omega
  have hn3 : 3 ≤ buSZ p + 8 := by have := buSZ_ge p; omega
  have ha : isz ((α : ℤ)) ≤ buSZ p + 8 := buDivB_isz_alpha_le p α hα hαp
  have hb : isz (buDivZ1 α) ≤ buSZ p + 8 := buDivB_isz_buDivZ1_le p α hαp
  have hc : isz (buDivZ2 α) ≤ buSZ p + 8 := buDivB_isz_buDivZ2_le p α hαp
  have he : isz ((2 : ℤ)) ≤ buSZ p + 8 := by
    have h := isz_const_le_buSZ p 2 (by norm_num)
    have h' : isz ((2 : ℤ)) ≤ buSZ p := by simpa using h
    have := buSZ_ge p
    omega
  have hKms : Kms ≤ Kms + Kd + Kad + Kpv + Ksw + Ksu + 1 := by omega
  have hKd : Kd ≤ Kms + Kd + Kad + Kpv + Ksw + Ksu + 1 := by omega
  have hKad : Kad ≤ Kms + Kd + Kad + Kpv + Ksw + Ksu + 1 := by omega
  have hKpv : Kpv ≤ Kms + Kd + Kad + Kpv + Ksw + Ksu + 1 := by omega
  have hKsw : Ksw ≤ Kms + Kd + Kad + Kpv + Ksw + Ksu + 1 := by omega
  have hKsu : Ksu ≤ Kms + Kd + Kad + Kpv + Ksw + Ksu + 1 := by omega
  -- `α · α` (`IntLib.mulS`)
  have s1 : Pipe main gms [Val.int (α : ℤ), Val.int (α : ℤ)] [Val.int (buDivZ1 α)]
      ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2) :=
    Pipe.le (Pipe.binOp (h := hms main) (a := (α : ℤ)) (b := (α : ℤ)) trivial) (by
      rw [mul_assoc]
      exact Nat.mul_le_mul hKms (buDivB_mul_le_sq ha ha))
  -- `dup`
  have s2 : Pipe main gdup [Val.int (buDivZ1 α)] [Val.int (buDivZ1 α), Val.int (buDivZ1 α)]
      ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2) :=
    Pipe.le (Pipe.dup main hdup (Val.int (buDivZ1 α))) (by
      rw [Work.Fx.vsz_int]
      exact Nat.mul_le_mul hKd (buDivB_succ_le_sq hn hb))
  -- `add`: `buDivZ2 α = 2α²`
  have s3 : Pipe main gadd [Val.int (buDivZ1 α), Val.int (buDivZ1 α)] [Val.int (buDivZ2 α)]
      ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2) :=
    Pipe.le (Pipe.binOp (h := hadd main) (a := buDivZ1 α) (b := buDivZ1 α) trivial) (by
      exact Nat.mul_le_mul hKad (buDivB_add_le_sq hn hb hb))
  -- push the constant `2`
  have s4 : Pipe main (gpv (Val.int 2)) [Val.int (buDivZ2 α)] [Val.int 2, Val.int (buDivZ2 α)]
      ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2) :=
    Pipe.le (Pipe.pushOnAny (h := hpv main (Val.int 2))) (by
      rw [Work.Fx.vsz_int]
      exact Nat.mul_le_mul hKpv (buDivB_succ_le_sq hn he))
  -- `swap`
  have s5 : Pipe main gsw [Val.int 2, Val.int (buDivZ2 α)] [Val.int (buDivZ2 α), Val.int 2]
      ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2) :=
    Pipe.le (Pipe.swap main hsw (Val.int 2) (Val.int (buDivZ2 α))) (by
      rw [Work.Fx.vsz_int, Work.Fx.vsz_int]
      exact Nat.mul_le_mul hKsw (add_buDivB_succ_le_sq hn3 he hc))
  -- `sub`: `buDivZ3 α = 2α² - 2`
  have s6 : Pipe main gsub [Val.int (buDivZ2 α), Val.int 2] [Val.int (buDivZ3 α)]
      ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2) :=
    Pipe.le (Pipe.binOp (h := hsub main) (a := buDivZ2 α) (b := (2 : ℤ)) trivial) (by
      exact Nat.mul_le_mul hKsu (buDivB_add_le_sq hn hc he))
  have c123456 : Pipe main (((((gms ;;; gdup) ;;; gadd) ;;; gpv (Val.int 2)) ;;; gsw) ;;; gsub)
      [Val.int (α : ℤ), Val.int (α : ℤ)] [Val.int (buDivZ3 α)]
      (((((((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2)
        + ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2))
        + ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2))
        + ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2))
        + ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2))
        + ((Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) * (buSZ p + 8) ^ 2)) :=
    Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp s1 s2) s3) s4) s5) s6
  refine Pipe.le (Pipe.appendTail ([Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] ++ V)
    c123456) ?_
  exact buDivB_six_le_eight (Kms + Kd + Kad + Kpv + Ksw + Ksu + 1) (buSZ p + 8)


/-- `buWd p α s t ℓ = Int.tdiv (auH p (buZb p α s t ℓ) (auNstep p)) ((2:ℤ)^(auPrec p - p + (2*α^2-2)))`
by definition, so the input window `[int (auH …)] ++ buCB p α s t` already holds the dividend.
The word must form the shift `k = auPrec p - p + (2*α^2-2)` as an integer on top of the window
(`pick` the `p` and `α` entries of `buCB` and use `IntLib.mulS`/`add`/`sub`; `p ≥ 100` gives
`auPrec p - p = 2*p+100`, and `α ≥ 2` gives `2*α^2-2 > 0`, so `k = 2*p+98+2*α^2` and the `ℕ` and `ℤ`
readings of `2*α^2-2` agree), then `swap` to put `auH …` back on top and apply `IntLib.shrT`
(`tdiv a (2^k.toNat)`); the shift exponent only needs `p` and `α`, both entries of `buCB`.
Size bounds: `isz_auH_le_buSZ`, `natAbs_buZb_le`, `natAbs_auH_le_buHQ` (`buKit`) for the dividend,
`Work.Resample.isz_p_le_buSZ` and `isz_natCast_le_buSZ_lt` (`buWdKit`) for the rest; the cost is
absorbed by `Work.Resample.buStepCost`, and `Work.Resample.pipe_to_wordR`/`spec_to_pipe` convert
between `Work.Fx.Spec` and `Pipe`. -/
theorem buWdDiv (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s)
      (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)),
      Work.Resample.Pipe main prog
        ([HvdH.Val.int (Work.Resample.auH p (Work.Resample.buZb p α s t ℓ) (Work.Resample.auNstep p))]
          ++ Work.Resample.buCB p α s t)
        ([HvdH.Val.int (Work.Resample.buWd p α s t ℓ)] ++ Work.Resample.buCB p α s t)
        (K * (p + 1) ^ K) := by
  -- the four phases of the shift word (proved in the sibling modules)
  obtain ⟨progA, KA, hA⟩ := buDivStepA KL
  obtain ⟨progB, KB, hB⟩ := buDivB KL IL
  obtain ⟨progC, KC, hC⟩ := buDivStepC KL IL
  obtain ⟨progD, KD, hD⟩ := buDivStepD KL IL
  refine ⟨HvdH.Cmd.seq progA (HvdH.Cmd.seq progB (HvdH.Cmd.seq progC progD)),
    256 * (KA + KB + KC + KD) + 256, ?_⟩
  intro main p α s t hs hst hα hp htp hαp ℓ hℓ hℓs
  -- the size bound for the dividend `auH ...`
  have hsp : s < 2 ^ p := by omega
  have hAd : HvdH.isz (auH p (buZb p α s t ℓ) (auNstep p)) ≤ buSZ p := by
    refine isz_auH_le_buSZ p (buZb p α s t ℓ) (auNstep p) hp ?_ le_rfl
    refine le_trans (natAbs_buZb_le p α s t ℓ (le_of_lt hαp) (by omega) hsp hp) ?_
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the tail of the canonical block
  let V : List HvdH.Val := [HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ),
    HvdH.Val.int ((egM p α : ℕ) : ℤ), HvdH.Val.int ((egN p α s t : ℕ) : ℤ), HvdH.Val.int (auPi p)]
  -- the four phases
  have h1 := hA main p α hα hαp (auH p (buZb p α s t ℓ) (auNstep p)) hAd V
  have h2 := hB main p α hα hαp (auH p (buZb p α s t ℓ) (auNstep p)) hAd V
  have h3 := hC main p α hα hαp (auH p (buZb p α s t ℓ) (auNstep p)) hAd V
  have h4 := hD main p α hα hαp (auH p (buZb p α s t ℓ) (auNstep p)) hAd V
  have hcomp : Pipe main (HvdH.Cmd.seq progA (HvdH.Cmd.seq progB (HvdH.Cmd.seq progC progD)))
      ([HvdH.Val.int (auH p (buZb p α s t ℓ) (auNstep p)), HvdH.Val.int (p : ℤ),
        HvdH.Val.int (α : ℤ)] ++ V)
      ([HvdH.Val.int (Int.tdiv (auH p (buZb p α s t ℓ) (auNstep p))
          ((2 : ℤ) ^ (auPrec p - p + (2 * α ^ 2 - 2)))), HvdH.Val.int (p : ℤ),
        HvdH.Val.int (α : ℤ)] ++ V)
      (KA * (buSZ p + 8) ^ 2 + (KB * (buSZ p + 8) ^ 2 +
        (KC * (buSZ p + 8) ^ 2 + KD * (buSZ p + 8) ^ 2))) :=
    Pipe.comp h1 (Pipe.comp h2 (Pipe.comp h3 h4))
  -- the composed word acts on the goal window
  have hmain : Pipe main (HvdH.Cmd.seq progA (HvdH.Cmd.seq progB (HvdH.Cmd.seq progC progD)))
      ([HvdH.Val.int (auH p (buZb p α s t ℓ) (auNstep p))] ++ buCB p α s t)
      ([HvdH.Val.int (buWd p α s t ℓ)] ++ buCB p α s t)
      (KA * (buSZ p + 8) ^ 2 + (KB * (buSZ p + 8) ^ 2 +
        (KC * (buSZ p + 8) ^ 2 + KD * (buSZ p + 8) ^ 2))) :=
    show Pipe main (HvdH.Cmd.seq progA (HvdH.Cmd.seq progB (HvdH.Cmd.seq progC progD)))
      ([HvdH.Val.int (auH p (buZb p α s t ℓ) (auNstep p))] ++ buCB p α s t)
      ([HvdH.Val.int (buWd p α s t ℓ)] ++ buCB p α s t)
      (KA * (buSZ p + 8) ^ 2 + (KB * (buSZ p + 8) ^ 2 +
        (KC * (buSZ p + 8) ^ 2 + KD * (buSZ p + 8) ^ 2))) from hcomp
  -- cost
  have hcost : KA * (buSZ p + 8) ^ 2 + (KB * (buSZ p + 8) ^ 2 +
        (KC * (buSZ p + 8) ^ 2 + KD * (buSZ p + 8) ^ 2))
      ≤ (256 * (KA + KB + KC + KD) + 256) * (p + 1) ^ (256 * (KA + KB + KC + KD) + 256) := by
    have hsum : KA * (buSZ p + 8) ^ 2 + (KB * (buSZ p + 8) ^ 2 +
        (KC * (buSZ p + 8) ^ 2 + KD * (buSZ p + 8) ^ 2))
        = (KA + KB + KC + KD) * (buSZ p + 8) ^ 2 := by ring
    rw [hsum]
    have h4 := buStepCost (KS := KA + KB + KC + KD) (p := p) (n := 4) hp (by norm_num)
    have hSnn : (0 : ℕ) ≤ KA + KB + KC + KD := Nat.zero_le _
    have hBnn : (0 : ℕ) ≤ (buSZ p + 8) ^ 2 := Nat.zero_le _
    nlinarith [h4, hSnn, hBnn]
  exact Pipe.le hmain hcost

end Work.Resample
