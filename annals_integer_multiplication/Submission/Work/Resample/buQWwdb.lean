import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWhints
import Submission.Work.ResMath.diagDp_entry_le_one
import Submission.Work.Resample.buZbClose
import Submission.Work.Resample.auH_err
import Submission.Work.Resample.auPiBound
import Submission.Work.ResMath.resE_defs

/-!
# `Work.Resample.buQWwdb`: the size bound `8·|buWd| ≤ 3·2^p` on the tabulated diagonal weights

`buWd p α s t ℓ = ⌊auH p (buZb p α s t ℓ) (auNstep p) / 2^{auPrec p - p + 2α²-2}⌋` is the tabulated
integer representative of `2^p · e^{π α² β_ℓ²} / 2^{2α²-2}` (`β_ℓ = buBeta s t ℓ / s`, `|β_ℓ| ≤ 1/2`).
The paper's `D'` is bounded by `3/8 · 2^p` uniformly in `α ≥ 2`: at `α = 2`, `β² = 1/4` the true
value is `2^p e^π / 2^6 = 0.3616·2^p` and the ratio `(3/8)/(e^π/2^6) = 24/e^π ≈ 1.037` is the whole
content of the estimate.

Four independent numerical inputs:

* `buQZbLe`: the fixed point exponent `buZb` is bounded by `2^{auPrec p}·α²(π/4 + 2^{-auPrec p})`
  (`buZbClose` + `|β| ≤ 1/2` + `α² ≥ 4`);
* `buQWAuHLeExp`: the Horner recursion satisfies
  `auH/2^P ≤ e^{buZb/2^P}·(1 + 2/2^P)` (`auH_err` + `pot ≤ exp`);
* `buQWdNum`: the pure real inequality
  `8·e^{α²(π/4 + 2^{-P})}(1 + 2/2^P)/2^{2α²-2} ≤ 3`, whose crux is `log 24 > π` (i.e. `e^π < 24`);
* the truncating division `tdiv ≤` division for a nonnegative numerator.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Work.Resample

open HvdH

/-! ## Elementary auxiliary facts -/

/-- `auPi p = uval (auPrec p)` is nonnegative. -/
lemma buQWAuPiNonneg (p : ℕ) : (0 : ℤ) ≤ auPi p := by
  rw [auPi, Work.Fx.uval]
  apply Int.fdiv_nonneg
  · rw [Work.Fx.Nval]
    exact add_nonneg (mul_nonneg (Int.natCast_nonneg _) (by positivity)) (by positivity)
  · positivity

/-- Truncating division of a nonnegative integer by a positive integer is bounded by the real
quotient. -/
lemma buQWTdivLeDiv (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    ((a.tdiv b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have h1 : b * a.tdiv b = a - a.tmod b := Int.mul_tdiv_self a b
  have h2 : 0 ≤ a.tmod b := Int.tmod_nonneg b ha
  have h3 : (b : ℝ) * ((a.tdiv b : ℤ) : ℝ) ≤ (a : ℝ) := by
    have h4 : ((b * a.tdiv b : ℤ) : ℝ) ≤ (a : ℝ) := by
      rw [h1]
      have h5 : ((a.tmod b : ℤ) : ℝ) ≥ 0 := by exact_mod_cast h2
      push_cast
      linarith
    calc (b : ℝ) * ((a.tdiv b : ℤ) : ℝ) = ((b * a.tdiv b : ℤ) : ℝ) := by push_cast; ring
      _ ≤ (a : ℝ) := h4
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  linarith

/-- Truncating division by the positive integer power `2^b`. -/
lemma buQWTdivPowLe (a : ℤ) (b : ℕ) (ha : 0 ≤ a) :
    ((a.tdiv ((2 : ℤ) ^ b) : ℤ) : ℝ) ≤ (a : ℝ) / (2 : ℝ) ^ b := by
  have h := buQWTdivLeDiv a ((2 : ℤ) ^ b) ha (by positivity)
  have hcast : (((2 : ℤ) ^ b : ℤ) : ℝ) = (2 : ℝ) ^ b := by push_cast; ring
  rwa [hcast] at h

/-- The Horner recursion `auH` is nonnegative for a nonnegative exponent. -/
lemma buQWAuHNonneg (p : ℕ) (Z : ℤ) (hZ : 0 ≤ Z) :
    ∀ j, j ≤ auNstep p → 0 ≤ auH p Z j := by
  intro j
  induction j with
  | zero => intro _; rw [show auH p Z 0 = (2 : ℤ) ^ (auPrec p) from rfl]; positivity
  | succ j ih =>
    intro hj
    have hj' : j ≤ auNstep p := by omega
    have hd : (0 : ℤ) < (auNstep p : ℤ) - (j : ℤ) := by
      have : j < auNstep p := by omega
      omega
    have h2p : (0 : ℤ) < (2 : ℤ) ^ (auPrec p) := by positivity
    have hprod : 0 ≤ Z * auH p Z j := mul_nonneg hZ (ih hj')
    have h1 : 0 ≤ Int.tdiv (Z * auH p Z j) ((2 : ℤ) ^ (auPrec p)) :=
      Int.tdiv_nonneg hprod (le_of_lt h2p)
    have h2 : 0 ≤ Int.tdiv (Int.tdiv (Z * auH p Z j) ((2 : ℤ) ^ (auPrec p)))
        ((auNstep p : ℤ) - (j : ℤ)) := Int.tdiv_nonneg h1 (le_of_lt hd)
    rw [show auH p Z (j + 1) = (2 : ℤ) ^ (auPrec p) +
        Int.tdiv (Int.tdiv (Z * auH p Z j) ((2 : ℤ) ^ (auPrec p)))
          ((auNstep p : ℤ) - (j : ℤ)) from rfl]
    linarith

/-! ## The upper bound for the fixed point Horner recursion -/

/-- `auH p Z (auNstep p)`, read at the working scale `2^{auPrec p}`, is bounded by
`e^{Z/2^{auPrec p}}·(1 + 2/2^{auPrec p})` for `Z ≥ 0`. -/
theorem buQWAuHLeExp (p : ℕ) (Z : ℤ) (hZ : 0 ≤ Z) :
    (auH p Z (auNstep p) : ℝ) / (2 : ℝ) ^ (auPrec p)
      ≤ Real.exp ((Z : ℝ) / (2 : ℝ) ^ (auPrec p))
        * (1 + 2 / (2 : ℝ) ^ (auPrec p)) := by
  have h2P : (0 : ℝ) < (2 : ℝ) ^ (auPrec p) := by positivity
  have hy0 : 0 ≤ (Z : ℝ) / (2 : ℝ) ^ (auPrec p) :=
    div_nonneg (by exact_mod_cast hZ) (le_of_lt h2P)
  have h1 := auH_err p Z (auNstep p) le_rfl
  rw [Nat.sub_self, abs_of_nonneg hy0] at h1
  have h2 : Work.Fx.pot ((Z : ℝ) / (2 : ℝ) ^ (auPrec p)) 0 (auNstep p + 1)
      ≤ Real.exp ((Z : ℝ) / (2 : ℝ) ^ (auPrec p)) :=
    Work.Fx.expRec.2.2.1 _ hy0 0 (auNstep p + 1)
  have h3 : (auH p Z (auNstep p) : ℝ) / (2 : ℝ) ^ (auPrec p)
      ≤ Work.Fx.pot ((Z : ℝ) / (2 : ℝ) ^ (auPrec p)) 0 (auNstep p + 1)
        + (2 / (2 : ℝ) ^ (auPrec p)) * Real.exp ((Z : ℝ) / (2 : ℝ) ^ (auPrec p)) := by
    have h4 := (abs_le.mp h1).2
    linarith
  calc (auH p Z (auNstep p) : ℝ) / (2 : ℝ) ^ (auPrec p)
      ≤ Work.Fx.pot ((Z : ℝ) / (2 : ℝ) ^ (auPrec p)) 0 (auNstep p + 1)
        + (2 / (2 : ℝ) ^ (auPrec p)) * Real.exp ((Z : ℝ) / (2 : ℝ) ^ (auPrec p)) := h3
    _ ≤ Real.exp ((Z : ℝ) / (2 : ℝ) ^ (auPrec p))
        + (2 / (2 : ℝ) ^ (auPrec p)) * Real.exp ((Z : ℝ) / (2 : ℝ) ^ (auPrec p)) := by
        linarith
    _ = Real.exp ((Z : ℝ) / (2 : ℝ) ^ (auPrec p))
        * (1 + 2 / (2 : ℝ) ^ (auPrec p)) := by ring

/-! ## The upper bound for the fixed point exponent `buZb` -/

/-- `buZb p α s t ℓ ≤ 2^{auPrec p}·α²(π/4 + 2^{-auPrec p})`: the exact exponent is
`2^P πα²β²` with `|β| ≤ 1/2`, and the two error terms are absorbed by `α² ≥ 4`. -/
theorem buQZbLe (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (hp : 100 ≤ p) (ℓ : ℤ) :
    ((buZb p α s t ℓ : ℤ) : ℝ) ≤ (2 : ℝ) ^ (auPrec p) *
      ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p))) := by
  have hs0 : 0 < s := by omega
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
  have hsRne : (s : ℝ) ≠ 0 := ne_of_gt hsR
  have hPi0 : (0 : ℤ) ≤ auPi p := buQWAuPiNonneg p
  have hPi1 : |(auPi p : ℝ) - (2 : ℝ) ^ (auPrec p) * Real.pi| ≤ 1 := auPiBound p hp
  obtain ⟨_, hZc⟩ := buZbClose p α s t hp hs0 ℓ hPi0 hPi1
  set β : ℝ := Work.ResMath.betaI s t ℓ with hβ
  have hβb : ((buBeta s t ℓ : ℤ) : ℝ) = (s : ℝ) * β := by
    rw [hβ]
    simp only [buBeta, Work.ResMath.betaI, HvdH.rnd]
    push_cast
    field_simp
  have hβle : |β| ≤ 1 / 2 := by rw [hβ]; exact Work.ResMath.betaI_abs_le s t ℓ
  have hβsq : β ^ 2 ≤ 1 / 4 := by
    have h1 : |β| ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg β) hβle 2
    rw [sq_abs] at h1
    norm_num at h1
    exact h1
  have hsq : (α : ℝ) ^ 2 * ((buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2
      = (α : ℝ) ^ 2 * β ^ 2 := by
    rw [hβb]
    field_simp
  rw [hsq] at hZc
  have hZc' : ((buZb p α s t ℓ : ℤ) : ℝ)
      ≤ (2 : ℝ) ^ (auPrec p) * (Real.pi * ((α : ℝ) ^ 2 * β ^ 2))
        + (1 + (α : ℝ) ^ 2 * β ^ 2) := by
    have h := (abs_le.mp hZc).2
    linarith
  have hα2 : (4 : ℝ) ≤ (α : ℝ) ^ 2 := by
    have h2 : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
    have h3 : (2 : ℝ) ^ 2 ≤ (α : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 2
    have h4 : ((2 : ℝ)) ^ 2 = 4 := by norm_num
    linarith [h3, h4]
  have hmulβ : (α : ℝ) ^ 2 * β ^ 2 ≤ (α : ℝ) ^ 2 * (1 / 4) :=
    mul_le_mul_of_nonneg_left hβsq (by positivity)
  have hpi4 : Real.pi * ((α : ℝ) ^ 2 * β ^ 2) ≤ Real.pi / 4 * (α : ℝ) ^ 2 := by
    have h1 : Real.pi * ((α : ℝ) ^ 2 * β ^ 2) ≤ Real.pi * ((α : ℝ) ^ 2 * (1 / 4)) :=
      mul_le_mul_of_nonneg_left hmulβ (le_of_lt Real.pi_pos)
    have h2 : Real.pi * ((α : ℝ) ^ 2 * (1 / 4)) = Real.pi / 4 * (α : ℝ) ^ 2 := by ring
    linarith [h1, h2]
  have h1plus : 1 + (α : ℝ) ^ 2 * β ^ 2 ≤ (α : ℝ) ^ 2 := by
    linarith [hmulβ, hα2]
  calc ((buZb p α s t ℓ : ℤ) : ℝ)
      ≤ (2 : ℝ) ^ (auPrec p) * (Real.pi * ((α : ℝ) ^ 2 * β ^ 2))
        + (1 + (α : ℝ) ^ 2 * β ^ 2) := hZc'
    _ ≤ (2 : ℝ) ^ (auPrec p) * (Real.pi / 4 * (α : ℝ) ^ 2) + (α : ℝ) ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_left hpi4 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (auPrec p))
        linarith
    _ = (2 : ℝ) ^ (auPrec p) * ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p))) := by
        have h2P : (2 : ℝ) ^ (auPrec p) ≠ 0 := by positivity
        field_simp

/-! ## Numerics: `e^π < 24`, `log 24 > π`, and the final real inequality -/

/-- `e^3 < 20.0856`. -/
lemma buQWExpThreeLt : Real.exp 3 < 20.0856 := by
  have h1 : Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    ring
  rw [h1]
  have h4 : (Real.exp 1) ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h5 : ((2.7182818286 : ℝ)) ^ 3 < 20.0856 := by norm_num
  linarith

/-- `e^π < 23.34`. -/
lemma buQWExpPiLt : Real.exp Real.pi < 23.34 := by
  have h1 : Real.exp Real.pi = Real.exp 3 * Real.exp (Real.pi - 3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (Real.pi - 3) ≤ 1.1617 := by
    have h3 : Real.pi - 3 ≤ (0.1416 : ℝ) := by linarith [Real.pi_lt_d20]
    have h4 : Real.exp (Real.pi - 3) ≤ Real.exp (0.1416 : ℝ) := Real.exp_le_exp.mpr h3
    have h5 : Real.exp (0.1416 : ℝ) ≤ 1.1617 := by
      have h := Real.abs_exp_sub_one_sub_id_le (x := (0.1416 : ℝ)) (by norm_num)
      have h6 := (abs_le.mp h).2
      nlinarith
    linarith
  rw [h1]
  have h7 : Real.exp 3 * Real.exp (Real.pi - 3) < 20.0856 * 1.1617 :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos buQWExpThreeLt h2 (Real.exp_pos 3).le (by norm_num)
  linarith [h7]

/-- `π + 1/100 < log 24`. -/
lemma buQWPiAddLog24 : Real.pi + 1 / 100 < Real.log 24 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 24)]
  have h1 : Real.exp (Real.pi + 1 / 100) = Real.exp Real.pi * Real.exp (1 / 100) := by
    rw [Real.exp_add]
  rw [h1]
  have h2 : Real.exp (1 / 100 : ℝ) ≤ 1.0102 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 100 : ℝ)) (by norm_num) (by norm_num)
    have h3 : (1 : ℝ) / (1 - 1 / 100) ≤ 1.0102 := by norm_num
    linarith
  have h4 : Real.exp Real.pi * Real.exp (1 / 100) < 23.34 * 1.0102 :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos buQWExpPiLt h2 (Real.exp_pos Real.pi).le (by norm_num)
  have h5 : (23.34 : ℝ) * 1.0102 < 24 := by norm_num
  linarith [h4, h5]

/-- `log (3/8) = 2 log 2 - log (32/3)`. -/
lemma buQWLog38 : Real.log (3 / 8 : ℝ) = 2 * Real.log 2 - Real.log (32 / 3) := by
  have h1 : Real.log (3 / 8 : ℝ) = Real.log 3 - Real.log 8 :=
    Real.log_div (by norm_num) (by norm_num)
  have h2 : Real.log (32 / 3 : ℝ) = Real.log 32 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have h3 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h4 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  rw [h1, h2, h3, h4]
  ring

/-- The key numeric inequality: `log (32/3) + 2/2^P ≤ 8 log 2 - π - 4/2^P`. -/
lemma buQWLogKey (p : ℕ) (hp : 100 ≤ p) :
    Real.log (32 / 3) + 2 * (1 / (2 : ℝ) ^ (auPrec p))
      ≤ 8 * Real.log 2 - Real.pi - 4 * (1 / (2 : ℝ) ^ (auPrec p)) := by
  have he0 : (0 : ℝ) < 1 / (2 : ℝ) ^ (auPrec p) := by positivity
  have h2P : (600 : ℝ) ≤ (2 : ℝ) ^ (auPrec p) := by
    have h10 : (600 : ℝ) ≤ (2 : ℝ) ^ 10 := by norm_num
    exact le_trans h10
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by simp only [auPrec]; omega))
  have hple : 6 * (1 / (2 : ℝ) ^ (auPrec p)) ≤ 1 / 100 := by
    have hx : (0 : ℝ) < (2 : ℝ) ^ (auPrec p) := by positivity
    rw [show 6 * (1 / (2 : ℝ) ^ (auPrec p)) = 6 / (2 : ℝ) ^ (auPrec p) by ring,
      div_le_iff₀ hx]
    linarith
  have h32 : Real.log (32 / 3) = 2 * Real.log 2 - Real.log (3 / 8 : ℝ) := by
    linarith [buQWLog38]
  have hlog24 : Real.log 24 = 6 * Real.log 2 + Real.log (3 / 8 : ℝ) := by
    have h1 : (24 : ℝ) = 2 ^ 6 * (3 / 8) := by norm_num
    rw [h1, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    norm_num
  have hfin : 8 * Real.log 2 - Real.log (32 / 3) = Real.log 24 := by
    rw [h32, hlog24]
    ring
  have h6 : 6 * (1 / (2 : ℝ) ^ (auPrec p)) ≤ Real.log 24 - Real.pi := by
    linarith [hple, buQWPiAddLog24]
  have h7 : 6 * (1 / (2 : ℝ) ^ (auPrec p))
      ≤ 8 * Real.log 2 - Real.log (32 / 3) - Real.pi := by
    rw [hfin]
    exact h6
  linarith [h7, he0]

/-- `(2^p)·2^{auPrec p - p + c} = 2^{auPrec p + c}`. -/
lemma buQWPowSplit (p c : ℕ) :
    (2 : ℝ) ^ p * (2 : ℝ) ^ (auPrec p - p + c) = (2 : ℝ) ^ (auPrec p + c) := by
  rw [← pow_add]
  congr 1
  simp only [auPrec]
  omega

/-- The pure numerical core of the `buWd` size bound. -/
theorem buQWdNum (p α : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) :
    8 * (Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
        * (1 + 2 / (2 : ℝ) ^ (auPrec p))) / (2 : ℝ) ^ (2 * α ^ 2 - 2) ≤ 3 := by
  have h2P : (0 : ℝ) < (2 : ℝ) ^ (auPrec p) := by positivity
  have heq : 2 / (2 : ℝ) ^ (auPrec p) = 2 * (1 / (2 : ℝ) ^ (auPrec p)) := by ring
  rw [heq]
  have hx4 : (4 : ℝ) ≤ (α : ℝ) ^ 2 := by
    have h2 : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
    have h3 : (2 : ℝ) ^ 2 ≤ (α : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 2
    have h4 : ((2 : ℝ)) ^ 2 = 4 := by norm_num
    linarith [h3, h4]
  have he100 : 1 / (2 : ℝ) ^ (auPrec p) ≤ 1 / 100 := by
    rw [div_le_iff₀ h2P]
    have h2P600 : (600 : ℝ) ≤ (2 : ℝ) ^ (auPrec p) := by
      have h10 : (600 : ℝ) ≤ (2 : ℝ) ^ 10 := by norm_num
      exact le_trans h10
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by simp only [auPrec]; omega))
    linarith
  have hA0 : 0 ≤ 2 * Real.log 2 - Real.pi / 4 - 1 / (2 : ℝ) ^ (auPrec p) := by
    have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h2 : Real.pi / 4 < 1 := by linarith [Real.pi_lt_four]
    linarith [h1, h2, he100]
  have hlogkey := buQWLogKey p hp
  have hexpArg : (α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p))
        + 2 * (1 / (2 : ℝ) ^ (auPrec p))
      ≤ Real.log (3 / 8) + ((2 * α ^ 2 - 2 : ℕ) : ℝ) * Real.log 2 := by
    have hcast : ((2 * α ^ 2 - 2 : ℕ) : ℝ) = 2 * (α : ℝ) ^ 2 - 2 := by
      have h2 : 2 ≤ 2 * α ^ 2 := by
        have h4 : 4 ≤ α ^ 2 := by simpa using (Nat.pow_le_pow_left hα 2)
        omega
      rw [Nat.cast_sub h2]
      push_cast
      ring
    rw [hcast, buQWLog38]
    have h1 : 4 * (2 * Real.log 2 - Real.pi / 4 - 1 / (2 : ℝ) ^ (auPrec p))
        ≤ (α : ℝ) ^ 2 * (2 * Real.log 2 - Real.pi / 4 - 1 / (2 : ℝ) ^ (auPrec p)) :=
      mul_le_mul_of_nonneg_right hx4 hA0
    linarith [h1, hlogkey]
  have hexp1 : Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
        * (1 + 2 * (1 / (2 : ℝ) ^ (auPrec p)))
      ≤ Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p))
          + 2 * (1 / (2 : ℝ) ^ (auPrec p))) := by
    have h1p : 1 + 2 * (1 / (2 : ℝ) ^ (auPrec p))
        ≤ Real.exp (2 * (1 / (2 : ℝ) ^ (auPrec p))) := by
      have h := Real.add_one_le_exp (2 * (1 / (2 : ℝ) ^ (auPrec p)))
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1p
      (Real.exp_pos ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))).le
    rwa [← Real.exp_add] at h2
  have hexp2 : Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p))
        + 2 * (1 / (2 : ℝ) ^ (auPrec p)))
      ≤ (3 / 8) * (2 : ℝ) ^ (2 * α ^ 2 - 2) := by
    have h := Real.exp_le_exp.mpr hexpArg
    have hrw : Real.exp (Real.log (3 / 8) + ((2 * α ^ 2 - 2 : ℕ) : ℝ) * Real.log 2)
        = (3 / 8) * (2 : ℝ) ^ (2 * α ^ 2 - 2) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 8), Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rwa [hrw] at h
  have hmain : Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
        * (1 + 2 * (1 / (2 : ℝ) ^ (auPrec p)))
      ≤ (3 / 8) * (2 : ℝ) ^ (2 * α ^ 2 - 2) := le_trans hexp1 hexp2
  have h2c : (0 : ℝ) < (2 : ℝ) ^ (2 * α ^ 2 - 2) := by positivity
  rw [div_le_iff₀ h2c]
  have hmul := mul_le_mul_of_nonneg_left hmain (by norm_num : (0 : ℝ) ≤ 8)
  rwa [show (8 : ℝ) * ((3 / 8) * (2 : ℝ) ^ (2 * α ^ 2 - 2))
      = 3 * (2 : ℝ) ^ (2 * α ^ 2 - 2) by ring] at hmul

/-! ## The target -/

theorem buQWwdb (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (ℓ : ℤ) :
    8 * (Work.Resample.buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p := by
  have hs0 : 0 < s := by omega
  have hPi0 : (0 : ℤ) ≤ auPi p := buQWAuPiNonneg p
  have hPi1 : |(auPi p : ℝ) - (2 : ℝ) ^ (auPrec p) * Real.pi| ≤ 1 := auPiBound p hp
  obtain ⟨hZ0, _⟩ := buZbClose p α s t hp hs0 ℓ hPi0 hPi1
  have hZle := buQZbLe p α s t hs hα hp ℓ
  have hE0 : 0 ≤ auH p (buZb p α s t ℓ) (auNstep p) :=
    buQWAuHNonneg p (buZb p α s t ℓ) hZ0 (auNstep p) le_rfl
  have hA := buQWAuHLeExp p (buZb p α s t ℓ) hZ0
  have hy : ((buZb p α s t ℓ : ℤ) : ℝ) / (2 : ℝ) ^ (auPrec p)
      ≤ (α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (auPrec p))]
    calc ((buZb p α s t ℓ : ℤ) : ℝ)
        ≤ (2 : ℝ) ^ (auPrec p) * ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p))) := hZle
      _ = (α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)) * (2 : ℝ) ^ (auPrec p) := by ring
  have hexpmono : Real.exp (((buZb p α s t ℓ : ℤ) : ℝ) / (2 : ℝ) ^ (auPrec p))
      ≤ Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p))) :=
    Real.exp_le_exp.mpr hy
  have hR : (auH p (buZb p α s t ℓ) (auNstep p) : ℝ) / (2 : ℝ) ^ (auPrec p)
      ≤ Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
        * (1 + 2 / (2 : ℝ) ^ (auPrec p)) := by
    have h2 := mul_le_mul_of_nonneg_left hexpmono
      (by positivity : (0 : ℝ) ≤ 1 + 2 / (2 : ℝ) ^ (auPrec p))
    linarith [hA, h2]
  have hEbound : (auH p (buZb p α s t ℓ) (auNstep p) : ℝ)
      ≤ (2 : ℝ) ^ (auPrec p)
        * (Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
          * (1 + 2 / (2 : ℝ) ^ (auPrec p))) := by
    have h2P : (0 : ℝ) < (2 : ℝ) ^ (auPrec p) := by positivity
    have h3 : (2 : ℝ) ^ (auPrec p)
          * ((auH p (buZb p α s t ℓ) (auNstep p) : ℝ) / (2 : ℝ) ^ (auPrec p))
        ≤ (2 : ℝ) ^ (auPrec p)
          * (Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
            * (1 + 2 / (2 : ℝ) ^ (auPrec p))) :=
      mul_le_mul_of_nonneg_left hR (le_of_lt h2P)
    have h4 : (2 : ℝ) ^ (auPrec p)
          * ((auH p (buZb p α s t ℓ) (auNstep p) : ℝ) / (2 : ℝ) ^ (auPrec p))
        = (auH p (buZb p α s t ℓ) (auNstep p) : ℝ) := by
      rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt h2P)]
    linarith [h3, h4]
  have hAnum := buQWdNum p α hα hp
  have hAbound : 8 * (Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
      * (1 + 2 / (2 : ℝ) ^ (auPrec p))) ≤ 3 * (2 : ℝ) ^ (2 * α ^ 2 - 2) := by
    have h2c : (0 : ℝ) < (2 : ℝ) ^ (2 * α ^ 2 - 2) := by positivity
    rw [div_le_iff₀ h2c] at hAnum
    exact hAnum
  have hbu : buWd p α s t ℓ
      = Int.tdiv (auH p (buZb p α s t ℓ) (auNstep p))
          ((2 : ℤ) ^ (auPrec p - p + (2 * α ^ 2 - 2))) := rfl
  have hbunn : 0 ≤ buWd p α s t ℓ := by
    rw [hbu]
    exact Int.tdiv_nonneg hE0 (by positivity)
  have hdiv : ((buWd p α s t ℓ : ℤ) : ℝ)
      ≤ (auH p (buZb p α s t ℓ) (auNstep p) : ℝ)
        / (2 : ℝ) ^ (auPrec p - p + (2 * α ^ 2 - 2)) := by
    rw [hbu]
    exact buQWTdivPowLe (auH p (buZb p α s t ℓ) (auNstep p))
      (auPrec p - p + (2 * α ^ 2 - 2)) hE0
  have hfinal : 8 * ((buWd p α s t ℓ : ℤ) : ℝ) ≤ 3 * (2 : ℝ) ^ p := by
    have h1 : 8 * ((buWd p α s t ℓ : ℤ) : ℝ)
        ≤ 8 * ((auH p (buZb p α s t ℓ) (auNstep p) : ℝ)
            / (2 : ℝ) ^ (auPrec p - p + (2 * α ^ 2 - 2))) := by linarith [hdiv]
    have h2 : 8 * ((auH p (buZb p α s t ℓ) (auNstep p) : ℝ)
        / (2 : ℝ) ^ (auPrec p - p + (2 * α ^ 2 - 2))) ≤ 3 * (2 : ℝ) ^ p := by
      rw [← mul_div_assoc]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (auPrec p - p + (2 * α ^ 2 - 2)))]
      have hkey : (3 : ℝ) * (2 : ℝ) ^ p * (2 : ℝ) ^ (auPrec p - p + (2 * α ^ 2 - 2))
          = 3 * (2 : ℝ) ^ (auPrec p + (2 * α ^ 2 - 2)) := by
        rw [mul_assoc, buQWPowSplit]
      rw [hkey]
      have h3 : 8 * (auH p (buZb p α s t ℓ) (auNstep p) : ℝ)
          ≤ 8 * ((2 : ℝ) ^ (auPrec p)
            * (Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
              * (1 + 2 / (2 : ℝ) ^ (auPrec p)))) := by linarith [hEbound]
      have h4 : 8 * ((2 : ℝ) ^ (auPrec p)
          * (Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
            * (1 + 2 / (2 : ℝ) ^ (auPrec p))))
          = (2 : ℝ) ^ (auPrec p)
            * (8 * (Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
              * (1 + 2 / (2 : ℝ) ^ (auPrec p)))) := by ring
      have h5 : (2 : ℝ) ^ (auPrec p)
          * (8 * (Real.exp ((α : ℝ) ^ 2 * (Real.pi / 4 + 1 / (2 : ℝ) ^ (auPrec p)))
            * (1 + 2 / (2 : ℝ) ^ (auPrec p))))
          ≤ (2 : ℝ) ^ (auPrec p) * (3 * (2 : ℝ) ^ (2 * α ^ 2 - 2)) :=
        mul_le_mul_of_nonneg_left hAbound (by positivity)
      have h6 : (2 : ℝ) ^ (auPrec p) * (3 * (2 : ℝ) ^ (2 * α ^ 2 - 2))
          = 3 * (2 : ℝ) ^ (auPrec p + (2 * α ^ 2 - 2)) := by
        rw [pow_add]
        ring
      linarith [h3, h4, h5, h6]
    linarith [h1, h2]
  have hnat : (((buWd p α s t ℓ).natAbs : ℕ) : ℝ) = ((buWd p α s t ℓ : ℤ) : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hbunn)
    simpa only [Int.cast_natCast] using h
  have hgoal : ((8 * (buWd p α s t ℓ).natAbs : ℕ) : ℝ) ≤ ((3 * 2 ^ p : ℕ) : ℝ) := by
    push_cast
    rw [hnat]
    exact hfinal
  exact_mod_cast hgoal

end Work.Resample
