import Submission.Work.GYCorr12
import Submission.Commons.NumberTheory.ArithmeticFunction.card_divisors_le_exp_log_div_loglog
import Submission.Commons.NumberTheory.Sieve.inv_mul_exp_log_div_loglog_le

/-!
# `GYCorr13`: the sharp `L^∞` bound for `ν = nuGT` and the `p`-free correlation condition

This file supplies the *sharp diagonal bound* which replaces the crude `Bnd` of `GYCorr11`, and
then instantiates `corrCond_of_gy_ub_pfree` (in `GYCorr12`) with the explicit `p`-free constant.

The pointwise bound is Green–Tao's: `ν(y) ≤ log R · d(W y + 1)²` and
`d(n) ≤ exp (C log n / log log n)` (the sub-polynomial divisor bound).  The factor `log R`
contributes `log log R` after taking logarithms, and `log log p ≤ log p / log log p`, so the total
`p⁻¹ (Mnu)^q` is bounded by an explicit function of `(m, q)` — see `Dcmax`.

Main output: `corrCond_nuGT_uniform`.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open GYMaj.BoxAvg
open Commons.NumberTheory.Sieve

variable {p : ℕ} [Fact p.Prime]
variable {m k : ℕ}

/-! ## 1. The sub-polynomial divisor constant -/

noncomputable def Cdv : ℝ :=
  Classical.choose (Commons.NumberTheory.ArithmeticFunction.card_divisors_le_exp_log_div_loglog)

lemma Cdv_pos : 0 < Cdv :=
  (Classical.choose_spec
    (Commons.NumberTheory.ArithmeticFunction.card_divisors_le_exp_log_div_loglog)).1

lemma card_divisors_le_Cdv {n N : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ N) :
    ((n.divisors.card : ℝ)) ≤
      Real.exp (Cdv * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ) + 2) + Cdv) :=
  (Classical.choose_spec
    (Commons.NumberTheory.ArithmeticFunction.card_divisors_le_exp_log_div_loglog)).2 n N h1 h2

/-- The exponent constant of the sharp bound, dominating `2 * Cdv`. -/
noncomputable def C1 : ℝ := 2 * Cdv + 2

lemma two_Cdv_le_C1 : 2 * Cdv ≤ C1 := by rw [C1]; linarith

lemma C1_pos : 0 < C1 := by rw [C1]; linarith [Cdv_pos]

/-- The `log`-scale `log (W N + 2) / log (log (W N + 2) + 2)` of the divisor bound. -/
noncomputable def psi (W N : ℕ) : ℝ :=
  Real.log ((W * N + 2 : ℕ) : ℝ) / Real.log (Real.log ((W * N + 2 : ℕ) : ℝ) + 2)

lemma psi_nonneg (W N : ℕ) : 0 ≤ psi W N := by
  rw [psi]
  refine div_nonneg ?_ ?_
  · refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ W * N + 2 := by omega
    exact_mod_cast this
  · refine Real.log_nonneg ?_
    have h1 : (1 : ℝ) ≤ ((W * N + 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ W * N + 2 := by omega
      exact_mod_cast this
    have := Real.log_nonneg h1
    linarith

/-- The sharp pointwise bound for `ν`. -/
noncomputable def Mnu (R W N : ℕ) : ℝ :=
  Real.exp (Real.log (Real.log (R : ℝ)) + C1 * psi W N + C1)

lemma Mnu_nonneg (R W N : ℕ) : 0 ≤ Mnu R W N := Real.exp_nonneg _

/-! ## 2. `ν ≤ Mnu` -/

/-- `Λ_R(n)² ≤ (log R · d(n))²`. -/
lemma LambdaR_sq_le_d {R n : ℕ} (hR : 1 ≤ R) :
    (LambdaR R n) ^ 2 ≤ (Real.log (R : ℝ) * ((n.divisors.card : ℝ))) ^ 2 := by
  have h := Commons.NumberTheory.Sieve.abs_LambdaR_le_log_mul_card (R := R) (n := n) hR
  have h2 : ((n.divisors.filter (fun d => d ≤ R)).card : ℝ) ≤ ((n.divisors.card : ℝ)) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have h3 : (0 : ℝ) ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  have h4 : Real.log (R : ℝ) * ((n.divisors.filter (fun d => d ≤ R)).card : ℝ)
      ≤ Real.log (R : ℝ) * ((n.divisors.card : ℝ)) := mul_le_mul_of_nonneg_left h2 h3
  have h5 : |LambdaR R n| ≤ Real.log (R : ℝ) * ((n.divisors.card : ℝ)) := le_trans h h4
  calc (LambdaR R n) ^ 2 = |LambdaR R n| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.log (R : ℝ) * ((n.divisors.card : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h5 2

/-- The basic `log`-size comparison `1 < log 3`. -/
lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]

/-- `1 ≤ log x` for `x ≥ 3`. -/
lemma one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : (1 : ℝ) ≤ Real.log x :=
  le_of_lt (lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hx))

/-- `1 < log x` for `x ≥ 3`. -/
lemma one_lt_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : (1 : ℝ) < Real.log x :=
  lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hx)

lemma nuGT_le_Mnu {R W : ℕ} {ε : ℝ} (hR : 3 ≤ R) (hW : 1 ≤ W) (y : ZMod p) :
    nuGT R W p ε y ≤ Mnu R W p := by
  have hR1 : 1 < R := by omega
  have hR1' : 1 ≤ R := by omega
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR1)
  have hbase : nuGT R W p ε y ≤ Real.log (R : ℝ) * Real.exp (C1 * psi W p + C1) := by
    by_cases hwin : ε * (p : ℝ) ≤ (y.val : ℝ) ∧ (y.val : ℝ) ≤ 2 * ε * (p : ℝ)
    · rw [nuGT, if_pos hwin]
      have hn1 : 1 ≤ W * y.val + 1 := by omega
      have hnle : W * y.val + 1 ≤ W * p + 2 := by
        have h1 : y.val + 1 ≤ p := by have := ZMod.val_lt y; omega
        calc W * y.val + 1 ≤ W * y.val + W := by omega
          _ = W * (y.val + 1) := by ring
          _ ≤ W * p := Nat.mul_le_mul_left _ h1
          _ ≤ W * p + 2 := by omega
      have hd := card_divisors_le_Cdv (n := W * y.val + 1) (N := W * p + 2) hn1 hnle
      have hd' : ((W * y.val + 1).divisors.card : ℝ) ≤ Real.exp (Cdv * psi W p + Cdv) := by
        simpa only [psi, mul_div_assoc] using hd
      have hφ : (Nat.totient W : ℝ) / (W : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (by omega : 0 < W))]
        exact_mod_cast Nat.totient_le W
      have hφ0 : 0 ≤ (Nat.totient W : ℝ) / (W : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hstep : (LambdaR R (W * y.val + 1)) ^ 2 / Real.log (R : ℝ)
          ≤ Real.log (R : ℝ) * ((W * y.val + 1).divisors.card : ℝ) ^ 2 := by
        rw [div_le_iff₀ hlogR]
        have hΛ := LambdaR_sq_le_d (R := R) (n := W * y.val + 1) hR1'
        nlinarith [hΛ, hlogR]
      calc nuBulk R W p y
          = (Nat.totient W : ℝ) / (W : ℝ)
              * ((LambdaR R (W * y.val + 1)) ^ 2 / Real.log (R : ℝ)) := rfl
        _ ≤ (Nat.totient W : ℝ) / (W : ℝ)
              * (Real.log (R : ℝ) * ((W * y.val + 1).divisors.card : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hstep hφ0
        _ ≤ 1 * (Real.log (R : ℝ) * ((W * y.val + 1).divisors.card : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hφ (by positivity)
        _ = Real.log (R : ℝ) * ((W * y.val + 1).divisors.card : ℝ) ^ 2 := one_mul _
        _ ≤ Real.log (R : ℝ) * (Real.exp (Cdv * psi W p + Cdv)) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ hlogR.le
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) hd' 2
        _ = Real.log (R : ℝ) * Real.exp (2 * (Cdv * psi W p + Cdv)) := by
            rw [← Real.exp_nat_mul]
            norm_num
        _ ≤ Real.log (R : ℝ) * Real.exp (C1 * psi W p + C1) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hlogR.le
            have hpsi := psi_nonneg W p
            have hC := two_Cdv_le_C1
            nlinarith
    · rw [nuGT, if_neg hwin]
      have h1 : (1 : ℝ) ≤ Real.log (R : ℝ) :=
        one_le_log_of_three_le (by exact_mod_cast hR)
      have h2 : (1 : ℝ) ≤ Real.exp (C1 * psi W p + C1) := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        exact add_nonneg (mul_nonneg (le_of_lt C1_pos) (psi_nonneg W p)) (le_of_lt C1_pos)
      nlinarith
  calc nuGT R W p ε y ≤ Real.log (R : ℝ) * Real.exp (C1 * psi W p + C1) := hbase
    _ = Real.exp (Real.log (Real.log (R : ℝ))) * Real.exp (C1 * psi W p + C1) := by
        rw [Real.exp_log hlogR]
    _ = Real.exp (Real.log (Real.log (R : ℝ)) + (C1 * psi W p + C1)) := by
        rw [← Real.exp_add]
    _ = Mnu R W p := by
        rw [Mnu]
        congr 1
        ring

/-- The product form of the sharp bound (used for the collision case). -/
lemma prod_nuGT_le_Mnu_pow {R W : ℕ} {ε : ℝ} (hR : 3 ≤ R) (hW : 1 ≤ W)
    (h : Fin m → ZMod p) (x : ZMod p) :
    ∏ i : Fin m, nuGT R W p ε (x + h i) ≤ Mnu R W p ^ m := by
  have h1 : ∏ i : Fin m, nuGT R W p ε (x + h i) ≤ ∏ _i : Fin m, Mnu R W p :=
    Finset.prod_le_prod (fun i _ => nuGT_nonneg (by omega : 1 < R) _)
      (fun i _ => nuGT_le_Mnu (p := p) hR hW _)
  rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1

/-! ## 3. The `p`-free power bound -/

/-- `log log p ≤ 4 log p / log log p` for `p ≥ 3`. -/
lemma loglog_le_four (hp3 : 3 ≤ p) :
    Real.log (Real.log (p : ℝ)) ≤ 4 * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ)) := by
  have hL1 : (1 : ℝ) < Real.log (p : ℝ) :=
    one_lt_log_of_three_le (by exact_mod_cast hp3)
  have hL1' : (0 : ℝ) < Real.log (p : ℝ) := by linarith
  have hs : 0 < Real.log (Real.log (p : ℝ)) := Real.log_pos hL1
  rw [le_div_iff₀ hs]
  have hexp : Real.exp (Real.log (Real.log (p : ℝ)) / 2) ≥ Real.log (Real.log (p : ℝ)) / 2 := by
    have := Real.add_one_le_exp (Real.log (Real.log (p : ℝ)) / 2)
    linarith
  have hsq : (Real.log (Real.log (p : ℝ))) ^ 2 ≤ 4 * Real.log (p : ℝ) := by
    have h' : (Real.log (Real.log (p : ℝ)) / 2) ^ 2
        ≤ (Real.exp (Real.log (Real.log (p : ℝ)) / 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hexp 2
    rw [← Real.exp_nat_mul] at h'
    norm_num at h'
    have h2 : (Real.exp (2 * (Real.log (Real.log (p : ℝ)) / 2)))
        = Real.log (p : ℝ) := by
      rw [show 2 * (Real.log (Real.log (p : ℝ)) / 2) = Real.log (Real.log (p : ℝ)) by ring,
        Real.exp_log hL1']
    rw [h2] at h'
    linarith [h']
  linarith [hsq]

/-- The argument of the exponential bound. -/
noncomputable def Atot (m q : ℕ) : ℝ := (4 + 3 * C1) * (m : ℝ) * (q : ℝ)

/-- The explicit `p`-free bound for `p⁻¹ · Mnu^{m q}`. -/
noncomputable def Dcmax (m q : ℕ) : ℝ :=
  Real.exp (max (12 * Atot m q) (Real.exp (Atot m q)) + C1 * (m : ℝ) * (q : ℝ))

lemma Atot_nonneg (m q : ℕ) : 0 ≤ Atot m q := by
  rw [Atot]
  have := le_of_lt C1_pos
  positivity

/-- **The `p`-free power bound.** -/
lemma Mnu_pow_le {R W : ℕ} (hR : 3 ≤ R) (hW : 1 ≤ W) (hWp : W ≤ p) (hRp : R ≤ p)
    (hp3 : 3 ≤ p) (m q : ℕ) (hq : 1 ≤ q) :
    (p : ℝ)⁻¹ * (Mnu R W p ^ m) ^ q ≤ Dcmax m q := by
  have hp1 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hL1 : (1 : ℝ) < Real.log (p : ℝ) := one_lt_log_of_three_le (by exact_mod_cast hp3)
  have hlogp : 0 < Real.log (p : ℝ) := by linarith
  have hloglogp : 0 < Real.log (Real.log (p : ℝ)) := Real.log_pos hL1
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hloglogR : Real.log (Real.log (R : ℝ)) ≤ Real.log (Real.log (p : ℝ)) :=
    Real.log_le_log hlogRpos (Real.log_le_log hRpos (by exact_mod_cast hRp))
  -- (i) the `log log R` piece
  have hmul1 : (m : ℝ) * (q : ℝ) * Real.log (Real.log (R : ℝ))
      ≤ (m : ℝ) * (q : ℝ) * (4 * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ))) :=
    mul_le_mul_of_nonneg_left (le_trans hloglogR (loglog_le_four hp3)) (by positivity)
  -- (ii) the `psi` piece
  have hnum1 : Real.log ((W * p + 2 : ℕ) : ℝ) ≤ 3 * Real.log (p : ℝ) := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 2 ≤ p)
    have hWpR : (W : ℝ) ≤ (p : ℝ) := by exact_mod_cast hWp
    have h1 : ((W * p + 2 : ℕ) : ℝ) ≤ (p : ℝ) ^ 3 := by
      have h2 : ((W * p + 2 : ℕ) : ℝ) = (W : ℝ) * (p : ℝ) + 2 := by push_cast; ring
      rw [h2]
      have hA : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
      have hB : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
      have hC : (4 : ℝ) ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 1) := by nlinarith [hA, hB]
      have hD : (p : ℝ) ^ 2 + 2 ≤ (p : ℝ) ^ 3 := by nlinarith [hC]
      calc (W : ℝ) * (p : ℝ) + 2 ≤ (p : ℝ) * (p : ℝ) + 2 := by nlinarith [hWpR, hp2]
        _ = (p : ℝ) ^ 2 + 2 := by ring
        _ ≤ (p : ℝ) ^ 3 := hD
    calc Real.log ((W * p + 2 : ℕ) : ℝ) ≤ Real.log ((p : ℝ) ^ 3) :=
          Real.log_le_log (by positivity) h1
      _ = 3 * Real.log (p : ℝ) := by rw [Real.log_pow]; push_cast; ring
  have hden1 : Real.log (Real.log (p : ℝ))
      ≤ Real.log (Real.log ((W * p + 2 : ℕ) : ℝ) + 2) := by
    refine Real.log_le_log hlogp ?_
    have h1 : Real.log (p : ℝ) ≤ Real.log ((W * p + 2 : ℕ) : ℝ) := by
      refine Real.log_le_log hp1 ?_
      have h2 : ((W * p + 2 : ℕ) : ℝ) = (W : ℝ) * (p : ℝ) + 2 := by push_cast; ring
      rw [h2]
      have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
      nlinarith
    linarith
  have hiii : psi W p ≤ 3 * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ)) := by
    rw [psi]
    exact div_le_div₀ (by positivity : (0 : ℝ) ≤ 3 * Real.log (p : ℝ)) hnum1 hloglogp hden1
  have hmul2 : (q : ℝ) * (C1 * (m : ℝ) * psi W p)
      ≤ (q : ℝ) * (C1 * (m : ℝ) * (3 * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ)))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hiii (mul_nonneg (le_of_lt C1_pos) (Nat.cast_nonneg m)))
      (Nat.cast_nonneg q)
  -- assemble
  have hA : ((m : ℝ) * (q : ℝ) * (4 * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ)))
        + (q : ℝ) * (C1 * (m : ℝ) * (3 * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ)))))
      = Atot m q * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ)) := by
    rw [Atot]
    field_simp
  have hb : (m : ℝ) * (q : ℝ) * Real.log (Real.log (R : ℝ))
        + (q : ℝ) * (C1 * (m : ℝ) * psi W p)
      ≤ Atot m q * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ)) := by
    rw [← hA]
    linarith [hmul1, hmul2]
  have hpow : (Mnu R W p ^ m) ^ q
      = Real.exp (C1 * (m : ℝ) * (q : ℝ)
          + ((m : ℝ) * (q : ℝ) * Real.log (Real.log (R : ℝ))
              + (q : ℝ) * (C1 * (m : ℝ) * psi W p))) := by
    rw [← pow_mul, Mnu, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv : (p : ℝ)⁻¹ = Real.exp (-(Real.log (p : ℝ))) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
  have hsplit : (p : ℝ)⁻¹ * Real.exp (C1 * (m : ℝ) * (q : ℝ)
        + ((m : ℝ) * (q : ℝ) * Real.log (Real.log (R : ℝ))
            + (q : ℝ) * (C1 * (m : ℝ) * psi W p)))
      = Real.exp (C1 * (m : ℝ) * (q : ℝ))
        * ((p : ℝ)⁻¹ * Real.exp ((m : ℝ) * (q : ℝ) * Real.log (Real.log (R : ℝ))
            + (q : ℝ) * (C1 * (m : ℝ) * psi W p))) := by
    rw [Real.exp_add]
    ring
  have hb1 : (p : ℝ)⁻¹ * Real.exp ((m : ℝ) * (q : ℝ) * Real.log (Real.log (R : ℝ))
        + (q : ℝ) * (C1 * (m : ℝ) * psi W p))
      ≤ Real.exp (max (12 * Atot m q) (Real.exp (Atot m q))) := by
    have h1 : Real.exp ((m : ℝ) * (q : ℝ) * Real.log (Real.log (R : ℝ))
          + (q : ℝ) * (C1 * (m : ℝ) * psi W p))
        ≤ Real.exp (Atot m q * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ))) :=
      Real.exp_le_exp.mpr hb
    calc (p : ℝ)⁻¹ * Real.exp ((m : ℝ) * (q : ℝ) * Real.log (Real.log (R : ℝ))
          + (q : ℝ) * (C1 * (m : ℝ) * psi W p))
        ≤ (p : ℝ)⁻¹ * Real.exp (Atot m q * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ Real.exp (max (12 * Atot m q) (Real.exp (Atot m q))) :=
          Commons.NumberTheory.Sieve.inv_mul_exp_log_div_loglog_le (Atot m q)
            (Atot_nonneg m q) p hp3
  calc (p : ℝ)⁻¹ * (Mnu R W p ^ m) ^ q
      = Real.exp (C1 * (m : ℝ) * (q : ℝ))
        * ((p : ℝ)⁻¹ * Real.exp ((m : ℝ) * (q : ℝ) * Real.log (Real.log (R : ℝ))
            + (q : ℝ) * (C1 * (m : ℝ) * psi W p))) := by rw [hpow, hsplit]
    _ ≤ Real.exp (C1 * (m : ℝ) * (q : ℝ))
        * Real.exp (max (12 * Atot m q) (Real.exp (Atot m q))) :=
        mul_le_mul_of_nonneg_left hb1 (Real.exp_nonneg _)
    _ = Dcmax m q := by
        rw [Dcmax, ← Real.exp_add]
        congr 1
        ring

lemma one_le_Ec {m : ℕ} (hm : 1 < m) : 1 ≤ Ec m := by
  have h2 : (2 : ℝ) ≤ Da m := by
    rw [Da]
    have h : (1 : ℝ) ≤ (24 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    exact le_trans (by linarith) (le_max_left _ _)
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
  have hm4 : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have h := Da_mul_sq_le_Ec m
  have h8 : (8 : ℝ) ≤ (Ec m : ℝ) := by nlinarith
  exact_mod_cast (by linarith : (1 : ℝ) ≤ (Ec m : ℝ))

/-! ## 4. The uniform correlation condition -/

theorem corrCond_nuGT_uniform {R W : ℕ} {ε_box εcorr εw : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hR : 3 ≤ R) (hRk : 3 * k ≤ R) (hW : 1 ≤ W)
    (hεbox0 : 0 ≤ ε_box) (hεbox1 : ε_box ≤ 1) (hεcorr0 : 0 < εcorr) (hεcorr1 : εcorr ≤ 1)
    (hεw : 0 < εw) (hεw4 : 4 * εw ≤ 1) (hεp1 : 1 ≤ εw * (p : ℝ))
    (hsmallEr : 6 * (3 * (k : ℝ)) * (Real.log (R : ℝ)) ^ (k * 2 ^ (k - 1))
      ≤ εcorr * (R : ℝ) ^ 6)
    (hsmallMn : ∀ a : ℕ, 1 ≤ a → a ≤ k * 2 ^ (k - 1) →
      4 * ((zbC a) ^ a * (EK a * stripBound W a)) ≤ (εcorr / 2) * Real.log (R : ℝ) * Kc a)
    (hside : (R : ℤ) ^ (10 * (k * 2 ^ (k - 1))) ≤ (p : ℤ))
    (hp3 : 3 ≤ p) (hWp : W ≤ p) (hRp : R ≤ p) :
    Commons.NumberTheory.Sieve.CorrCond p (nuGT R W p εw) (2 ^ (k - 1))
      (fun m q => max 1 (Dcmax m q + (Kmax m) ^ q * (2 * CwMoment (Ec m * q)))) := by
  classical
  have hεc0 : 0 ≤ εcorr := le_of_lt hεcorr0
  have hR1 : 1 < R := by omega
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : p.Prime))
  have hRz : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast (by omega : 1 ≤ R)
  refine corrCond_of_gy_ub_pfree hp3 (nuGT R W p εw) (2 ^ (k - 1))
    (K := fun m => Kcorr ε_box εcorr m) (Dc := fun m => Mnu R W p ^ m)
    (fun m => Kcorr_nonneg ε_box εcorr hεbox0 hεc0 m)
    (fun m => pow_nonneg (Mnu_nonneg R W p) m) (E := Ec)
    (fun m hm1 => one_le_Ec hm1) ?_
    (Kmax := Kmax) (fun m => Kmax_nonneg m)
    (fun m => Kcorr_le_Kmax hεbox1 hεcorr1 m) (S := Dcmax)
    (fun m q hq => Mnu_pow_le hR hW hWp hRp hp3 m q hq)
  intro m hm1 hm2 h
  have hm2' : 2 ≤ m := hm1
  have hmk : m ≤ k * 2 ^ (k - 1) := by
    refine le_trans hm2 ?_
    calc 2 ^ (k - 1) = 1 * 2 ^ (k - 1) := (one_mul _).symm
      _ ≤ (k : ℕ) * 2 ^ (k - 1) := Nat.mul_le_mul_right _ hk
  have hAcard : ∀ A ∈ (Finset.univ : Finset (Fin m)).powerset, A.card ≤ k * 2 ^ (k - 1) := by
    intro A _
    have h1 : A.card ≤ m := by
      have := Finset.card_le_univ A
      simpa using this
    exact le_trans h1 hmk
  have hP1 : 1 ≤ Pw h (Ec m) := one_le_Pw hm2' h (Ec m)
  by_cases hinj : Function.Injective h
  · have hstep : (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i)
        ≤ Kcorr ε_box εcorr m * Pw h (Ec m) := by
      have h1 : (∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i))
          ≤ ∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
              ∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i) := by
        refine le_trans (Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (ZMod p))) =>
          prod_nuGT_le_sum_gGT (W := W) (ε := εw) hR1 h x)) ?_
        rw [Finset.sum_comm]
      refine le_trans (mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Nat.cast_nonneg p))) ?_
      rw [Finset.mul_sum]
      have hper : ∀ A ∈ (Finset.univ : Finset (Fin m)).powerset,
          (p : ℝ)⁻¹ * (∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i))
            ≤ Ktil ε_box εcorr m * Pw h (Ec m) := by
        intro A hA
        rw [Finset.mem_powerset] at hA
        by_cases hAe : A = ∅
        · subst hAe
          have hsum : ∑ x : ZMod p, ∏ i ∈ (∅ : Finset (Fin m)), gGT R W p εw (x + h i)
              = (p : ℝ) := by
            have hc : ∀ x : ZMod p,
                (∏ i ∈ (∅ : Finset (Fin m)), gGT R W p εw (x + h i)) = (1 : ℝ) :=
              fun x => Finset.prod_empty
            simp only [hc, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
          rw [hsum, inv_mul_cancel₀ hp0]
          have honeK : (1 : ℝ) ≤ Ktil ε_box εcorr m := one_le_Ktil ε_box εcorr hεbox0 hεc0 m
          nlinarith [honeK, hP1]
        · refine gTerm_le (k := k) (R := R) (W := W) (p := p) (A := A)
            (Finset.nonempty_iff_ne_empty.mpr hAe) (hAcard A (Finset.mem_powerset.mpr hA))
            hinj hk hR hRk hW hεbox0 hεcorr0 hεw hεw4 hεp1 hm2' hsmallEr hsmallMn ?_
          have hc : A.card ≤ k * 2 ^ (k - 1) := hAcard A (Finset.mem_powerset.mpr hA)
          have hm : 10 * A.card ≤ 10 * (k * 2 ^ (k - 1)) := by omega
          exact le_trans (pow_le_pow_right₀ hRz hm) hside
      calc ∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
            (p : ℝ)⁻¹ * (∑ x : ZMod p, ∏ i ∈ A, gGT R W p εw (x + h i))
          ≤ ∑ _A ∈ (Finset.univ : Finset (Fin m)).powerset,
              Ktil ε_box εcorr m * Pw h (Ec m) := Finset.sum_le_sum hper
        _ = 2 ^ m * (Ktil ε_box εcorr m * Pw h (Ec m)) := by
            rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            push_cast
            ring
        _ = Kcorr ε_box εcorr m * Pw h (Ec m) := by rw [Kcorr]; ring
    calc (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i)
        ≤ Kcorr ε_box εcorr m * Pw h (Ec m) := hstep
      _ = ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
            (if h i = h j then Mnu R W p ^ m
             else Kcorr ε_box εcorr m
               * (∏ q ∈ (min (h i - h j).val (p - (h i - h j).val)).primeFactors,
                     (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (Ec m)) := by
          rw [Pw, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [Finset.mem_filter] at hj
          have hne : h i ≠ h j := fun hc => absurd (hinj hc) (ne_of_lt hj.2)
          rw [if_neg hne, Vw]
  · have hcoll : ∃ i j : Fin m, i ≠ j ∧ h i = h j := by
      by_contra hc
      push_neg at hc
      exact hinj (fun a b hab => by
        by_contra hne
        exact hc a b hne hab)
    obtain ⟨i, j, hij, heq⟩ := hcoll
    have hLHS : (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i)
        ≤ Mnu R W p ^ m := by
      have h1 : ∀ x : ZMod p, (∏ i : Fin m, nuGT R W p εw (x + h i)) ≤ Mnu R W p ^ m :=
        fun x => prod_nuGT_le_Mnu_pow (p := p) hR hW h x
      have h2 : (∑ x : ZMod p, ∏ i : Fin m, nuGT R W p εw (x + h i))
          ≤ ∑ _x : ZMod p, Mnu R W p ^ m := Finset.sum_le_sum (fun x _ => h1 x)
      have h3 : (∑ _x : ZMod p, Mnu R W p ^ m) = (p : ℝ) * Mnu R W p ^ m := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [h3] at h2
      have h4 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (Nat.cast_nonneg p))
      have h5 : (p : ℝ)⁻¹ * ((p : ℝ) * Mnu R W p ^ m) = Mnu R W p ^ m := by
        rw [← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
      rw [h5] at h4
      exact h4
    set F : Fin m → Fin m → ℝ := fun i' j' => (if h i' = h j' then Mnu R W p ^ m
        else Kcorr ε_box εcorr m
          * (∏ q ∈ (min (h i' - h j').val (p - (h i' - h j').val)).primeFactors,
                (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (Ec m)) with hF
    have hnn : ∀ i' j' : Fin m, 0 ≤ F i' j' := by
      intro i' j'
      change 0 ≤ (if h i' = h j' then Mnu R W p ^ m
        else Kcorr ε_box εcorr m
          * (∏ q ∈ (min (h i' - h j').val (p - (h i' - h j').val)).primeFactors,
                (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (Ec m))
      by_cases hc : h i' = h j'
      · rw [if_pos hc]; exact pow_nonneg (Mnu_nonneg R W p) m
      · rw [if_neg hc]
        exact mul_nonneg (Kcorr_nonneg ε_box εcorr hεbox0 hεc0 m) (pow_nonneg (Vw_nonneg _) _)
    have hRHS : Mnu R W p ^ m ≤ ∑ i' : Fin m,
        ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j' := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hmem : j ∈ Finset.univ.filter (fun j' : Fin m => i < j') := by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩
        have hii : F i j = Mnu R W p ^ m := by rw [hF]; exact if_pos heq
        calc Mnu R W p ^ m = F i j := hii.symm
          _ ≤ ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i < j'), F i j' :=
              Finset.single_le_sum (f := fun j' : Fin m => F i j')
                (fun j' _ => hnn i j') hmem
          _ ≤ ∑ i' : Fin m, ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j' :=
              Finset.single_le_sum
                (f := fun i' : Fin m =>
                  ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j')
                (fun i' _ => Finset.sum_nonneg (fun j' _ => hnn i' j')) (Finset.mem_univ i)
      · have hmem : i ∈ Finset.univ.filter (fun j' : Fin m => j < j') := by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt⟩
        have hii : F j i = Mnu R W p ^ m := by rw [hF]; exact if_pos heq.symm
        calc Mnu R W p ^ m = F j i := hii.symm
          _ ≤ ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => j < j'), F j j' :=
              Finset.single_le_sum (f := fun j' : Fin m => F j j')
                (fun j' _ => hnn j j') hmem
          _ ≤ ∑ i' : Fin m, ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j' :=
              Finset.single_le_sum
                (f := fun i' : Fin m =>
                  ∑ j' ∈ Finset.univ.filter (fun j' : Fin m => i' < j'), F i' j')
                (fun i' _ => Finset.sum_nonneg (fun j' _ => hnn i' j')) (Finset.mem_univ j)
    rw [hF] at hRHS
    exact le_trans hLHS hRHS

end Corr
end GYMaj
