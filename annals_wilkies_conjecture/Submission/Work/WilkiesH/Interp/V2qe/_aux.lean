import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params
import Submission.Work.WilkiesH.Interp.monoCount_bounds
import Submission.Work.WilkiesH.Interp.V2qb.Qval

/-!
# Numerical auxiliary estimates for the `log (1/ε)` bound

Self-contained helper lemmas needed by `q_bound_eps`: elementary size estimates for
`bV`, `dV`, `qval`, the `(μ+1)`-st-root bound for `qval`, the logarithm of `1/epsV`,
and the `μ/(μ+1)`-power shrinking machinery.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section
open Classical

namespace Work.WilkiesH.Interp.V2qe

open Work.WilkiesH.Interp V2qb

/-! ## Elementary estimates -/

lemma log_nat_le_succ (n : ℕ) : Real.log (n : ℝ) ≤ (n : ℝ) + 1 := by
  have h := Real.log_le_self (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))
  linarith

lemma one_le_thousand_cube (μ : ℕ) : (1 : ℕ) ≤ 1000 * (μ + 1) ^ 3 := by
  have h1 : (1:ℕ) ≤ (μ+1)^3 := Nat.one_le_pow 3 (μ+1) (by omega)
  calc (1:ℕ) = 1 * 1 := by ring
    _ ≤ 1000 * (μ+1)^3 := Nat.mul_le_mul (by norm_num) h1

lemma two_le_thousand_cube (μ : ℕ) : (2 : ℕ) ≤ 1000 * (μ + 1) ^ 3 := by
  have h1 : (1:ℕ) ≤ (μ+1)^3 := Nat.one_le_pow 3 (μ+1) (by omega)
  calc (2:ℕ) = 2 * 1 := by ring
    _ ≤ 1000 * (μ+1)^3 := Nat.mul_le_mul (by norm_num) h1

lemma three_le_thousand_cube (μ : ℕ) : (3 : ℕ) ≤ 1000 * (μ + 1) ^ 3 := by
  have h1 : (1:ℕ) ≤ (μ+1)^3 := Nat.one_le_pow 3 (μ+1) (by omega)
  calc (3:ℕ) = 3 * 1 := by ring
    _ ≤ 1000 * (μ+1)^3 := Nat.mul_le_mul (by norm_num) h1

lemma AA_succ_le_EcV (μ : ℕ) : AA μ + 1 ≤ Ec μ := by
  rw [AA, Ec]
  have h3 : (μ+1)^3 ≤ (μ+1)^4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : (1:ℕ) ≤ (μ+1)^3 := Nat.one_le_pow 3 (μ+1) (by omega)
  nlinarith [h3, h1]

/-- `(μ+2)^(100(μ+1)²) = CCc μ` as real numbers. -/
lemma pow_eq_CCc (μ : ℕ) : ((μ:ℝ)+2)^(100*(μ+1)^2) = (CCc μ : ℝ) := by
  have hb : ((μ:ℝ)+2) = (((μ+2 : ℕ)) : ℝ) := by push_cast; ring
  rw [hb, ← Nat.cast_pow, CCc]

/-- `2^60 (μ+2) ≤ CCc μ`. -/
lemma CCc_ge_two_pow_mul (μ : ℕ) : (2:ℝ)^60 * ((μ:ℝ)+2) ≤ (CCc μ : ℝ) := by
  have hm : (2:ℝ) ≤ (μ:ℝ)+2 := by linarith [nat_cast_nonneg_R μ]
  have h1 : (2:ℝ)^60 ≤ ((μ:ℝ)+2)^99 := by
    calc (2:ℝ)^60 ≤ (2:ℝ)^99 := by norm_num
      _ ≤ ((μ:ℝ)+2)^99 := pow_le_pow_left₀ (by norm_num) hm 99
  have h2 : (2:ℝ)^60 * ((μ:ℝ)+2) ≤ ((μ:ℝ)+2)^99 * ((μ:ℝ)+2) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : ((μ:ℝ)+2)^99 * ((μ:ℝ)+2) = ((μ:ℝ)+2)^100 := by rw [← pow_succ]
  have h4 : ((μ:ℝ)+2)^100 ≤ ((μ:ℝ)+2)^(100*(μ+1)^2) := by
    apply pow_le_pow_right₀ (by linarith)
    have h : 1 ≤ (μ+1)^2 := Nat.one_le_pow 2 (μ+1) (by omega)
    calc (100:ℕ) = 100*1 := by ring
      _ ≤ 100*(μ+1)^2 := Nat.mul_le_mul_left 100 h
  calc (2:ℝ)^60 * ((μ:ℝ)+2) ≤ ((μ:ℝ)+2)^99 * ((μ:ℝ)+2) := h2
    _ = ((μ:ℝ)+2)^100 := h3
    _ ≤ ((μ:ℝ)+2)^(100*(μ+1)^2) := h4
    _ = (CCc μ : ℝ) := pow_eq_CCc μ

/-- From `C ≤ 2^60 (μ+2)^2` conclude `C ≤ (μ+2)^(100(μ+1))`. -/
lemma le_pow_mu (μ : ℕ) {C : ℝ} (hC : C ≤ (2:ℝ)^60 * ((μ:ℝ)+2)^2) :
    C ≤ ((μ:ℝ)+2)^(100*(μ+1)) := by
  have hm : (2:ℝ) ≤ (μ:ℝ)+2 := by linarith [nat_cast_nonneg_R μ]
  have hx0 : (0:ℝ) ≤ (μ:ℝ)+2 := by linarith
  have h98 : ((μ:ℝ)+2)^2 * (2:ℝ)^98 ≤ ((μ:ℝ)+2)^100 := by
    have h1 : (2:ℝ)^98 ≤ ((μ:ℝ)+2)^98 := pow_le_pow_left₀ (by norm_num) hm 98
    have h2 : ((μ:ℝ)+2)^2 * (2:ℝ)^98 ≤ ((μ:ℝ)+2)^2 * ((μ:ℝ)+2)^98 :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hx0 2)
    have h3 : ((μ:ℝ)+2)^2 * ((μ:ℝ)+2)^98 = ((μ:ℝ)+2)^100 := by rw [← pow_add]
    calc ((μ:ℝ)+2)^2 * (2:ℝ)^98 ≤ ((μ:ℝ)+2)^2 * ((μ:ℝ)+2)^98 := h2
      _ = ((μ:ℝ)+2)^100 := h3
  have h260 : (2:ℝ)^60 ≤ (2:ℝ)^98 := by norm_num
  have h100 : ((μ:ℝ)+2)^100 ≤ ((μ:ℝ)+2)^(100*(μ+1)) := by
    apply pow_le_pow_right₀ (by linarith)
    have h : 1 ≤ μ+1 := by omega
    calc (100:ℕ) = 100*1 := by ring
      _ ≤ 100*(μ+1) := Nat.mul_le_mul_left 100 h
  calc C ≤ (2:ℝ)^60 * ((μ:ℝ)+2)^2 := hC
    _ ≤ (2:ℝ)^98 * ((μ:ℝ)+2)^2 := mul_le_mul_of_nonneg_right h260 (pow_nonneg hx0 2)
    _ = ((μ:ℝ)+2)^2 * (2:ℝ)^98 := by ring
    _ ≤ ((μ:ℝ)+2)^100 := h98
    _ ≤ ((μ:ℝ)+2)^(100*(μ+1)) := h100

/-- `EE μ · (μ+2)^(60(μ+1)²) = CCc μ`. -/
lemma EE_mul_pow_CCc (μ : ℕ) :
    (EE μ : ℝ) * ((μ:ℝ)+2)^(60*(μ+1)^2) = (CCc μ : ℝ) := by
  rw [EE, CCc]
  push_cast
  rw [← pow_add]
  congr 1
  ring

/-- `8 log (KK μ) ≤ (μ+2)^(60(μ+1)²)`. -/
lemma log_KK_le_eight (μ : ℕ) :
    8 * Real.log ((KK μ : ℕ) : ℝ) ≤ ((μ:ℝ)+2)^(60*(μ+1)^2) := by
  have hK : ((KK μ : ℕ) : ℝ) = 2*((μ:ℝ)+2) := by
    simp only [KK]
    push_cast
    ring
  have hx2 : (2:ℝ) ≤ (μ:ℝ)+2 := by linarith [nat_cast_nonneg_R μ]
  have hpos : (0:ℝ) < 2*((μ:ℝ)+2) := by linarith
  have hlog : Real.log (2*((μ:ℝ)+2)) ≤ 2*((μ:ℝ)+2) := Real.log_le_self (le_of_lt hpos)
  have h8 : 8 * Real.log (2*((μ:ℝ)+2)) ≤ 8 * (2*((μ:ℝ)+2)) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have h16 : (16:ℝ) * ((μ:ℝ)+2) ≤ ((μ:ℝ)+2)^6 := by
    have h5 : (16:ℝ) ≤ ((μ:ℝ)+2)^5 := by
      calc (16:ℝ) ≤ (2:ℝ)^5 := by norm_num
        _ ≤ ((μ:ℝ)+2)^5 := pow_le_pow_left₀ (by norm_num) hx2 5
    calc (16:ℝ) * ((μ:ℝ)+2) ≤ ((μ:ℝ)+2)^5 * ((μ:ℝ)+2) :=
          mul_le_mul_of_nonneg_right h5 (by linarith)
      _ = ((μ:ℝ)+2)^6 := by rw [← pow_succ]
  have h6 : ((μ:ℝ)+2)^6 ≤ ((μ:ℝ)+2)^(60*(μ+1)^2) := by
    apply pow_le_pow_right₀ (by linarith)
    have h : 1 ≤ (μ+1)^2 := Nat.one_le_pow 2 (μ+1) (by omega)
    calc (6:ℕ) = 6*1 := by ring
      _ ≤ 60*(μ+1)^2 := Nat.mul_le_mul (by norm_num) h
  rw [hK]
  calc 8 * Real.log (2*((μ:ℝ)+2)) ≤ 8 * (2*((μ:ℝ)+2)) := h8
    _ = 16*((μ:ℝ)+2) := by ring
    _ ≤ ((μ:ℝ)+2)^6 := h16
    _ ≤ ((μ:ℝ)+2)^(60*(μ+1)^2) := h6

/-- `log N1V ≤ (μ+1)(d+1)`. -/
lemma log_N1V_le (μ g H : ℕ) :
    Real.log (((N1V μ g H : ℕ)) : ℝ) ≤ ((μ:ℝ)+1) * ((((dV μ g (bV μ g H) : ℕ)) : ℝ) + 1) := by
  have hle : N1V μ g H ≤ (dV μ g (bV μ g H) + 1) ^ (μ + 1) := by
    have := (monoCount_bounds (μ + 1) (dV μ g (bV μ g H)) 0).1
    simpa only [N1V] using this
  have hN1pos : (0:ℝ) < ((N1V μ g H : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_N1V μ g H)
  have hbpos : (0:ℝ) < ((dV μ g (bV μ g H) : ℕ) : ℝ) + 1 := by
    have := nat_cast_nonneg_R (dV μ g (bV μ g H)); linarith
  have hμ1 : (0:ℝ) ≤ (μ:ℝ) + 1 := by linarith [nat_cast_nonneg_R μ]
  have hpow : ((N1V μ g H : ℕ) : ℝ) ≤ (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1)^(μ+1) := by
    have h : ((N1V μ g H : ℕ) : ℝ) ≤ ((((dV μ g (bV μ g H) + 1) ^ (μ+1) : ℕ)) : ℝ) := by
      exact_mod_cast hle
    simpa using h
  have hlog := Real.log_le_log hN1pos hpow
  rw [Real.log_pow] at hlog
  have hcastμ : (((μ+1 : ℕ)) : ℝ) = (μ:ℝ)+1 := by push_cast; ring
  rw [hcastμ] at hlog
  calc Real.log ((N1V μ g H : ℕ) : ℝ)
      ≤ ((μ:ℝ)+1) * Real.log (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1) := hlog
    _ ≤ ((μ:ℝ)+1) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_self (le_of_lt hbpos)) hμ1

/-! ## `M^(μ/(μ+1))`-shrinking machinery -/

lemma rpow_split (M : ℝ) (hM : 0 < M) (μ : ℕ) :
    M^((μ:ℝ)/((μ:ℝ)+1)) * M^(1/((μ:ℝ)+1)) = M := by
  rw [← Real.rpow_add hM]
  have h : (μ:ℝ)/((μ:ℝ)+1) + 1/((μ:ℝ)+1) = 1 := by
    have hμ : ((μ:ℝ)+1) ≠ 0 := by linarith [nat_cast_nonneg_R μ]
    field_simp
  rw [h, Real.rpow_one]

lemma const_rpow_mul_le (μ : ℕ) (M : ℝ) (hM : 0 < M) (X : ℝ)
    (hX : X ≤ M^(1/((μ:ℝ)+1))) : X * M^((μ:ℝ)/((μ:ℝ)+1)) ≤ M := by
  calc X * M^((μ:ℝ)/((μ:ℝ)+1))
      ≤ M^(1/((μ:ℝ)+1)) * M^((μ:ℝ)/((μ:ℝ)+1)) :=
        mul_le_mul_of_nonneg_right hX (Real.rpow_nonneg (le_of_lt hM) _)
    _ = M^((μ:ℝ)/((μ:ℝ)+1)) * M^(1/((μ:ℝ)+1)) := by ring
    _ = M := rpow_split M hM μ

/-- From `X^(μ+1) ≤ M` and `0 ≤ X` conclude `X ≤ M^(1/(μ+1))`. -/
lemma rpow_ge_of_pow_le (μ : ℕ) {X M : ℝ} (hX : 0 ≤ X) (h : X^(μ+1) ≤ M) :
    X ≤ M^(1/((μ:ℝ)+1)) := by
  have hn : μ + 1 ≠ 0 := by omega
  have h1 : (X^(μ+1))^((((μ+1 : ℕ)) : ℝ)⁻¹) = X := Real.pow_rpow_inv_natCast hX hn
  have h2 : (X^(μ+1))^(1/((μ:ℝ)+1)) = X := by
    have hcast : (((μ+1 : ℕ)) : ℝ) = (μ:ℝ)+1 := by push_cast; ring
    rw [← hcast, one_div]
    exact h1
  rw [← h2]
  exact Real.rpow_le_rpow (pow_nonneg hX _) h (one_div_pos.mpr (by linarith [nat_cast_nonneg_R μ] : (0:ℝ) < (μ:ℝ)+1)).le

/-- The key shrinking estimate: `C (1+g)^k (1+log H)^m ≤ qval^(1/(μ+1))` whenever
`C ≤ (μ+2)^(100(μ+1))` and `k, m ≤ 1000(μ+1)^3`. -/
lemma qval_rpow_key (μ D g H : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ ((μ:ℝ)+2)^(100*(μ+1))) {k m : ℕ}
    (hk : k ≤ 1000*(μ+1)^3) (hm : m ≤ 1000*(μ+1)^3) :
    C * (1 + (g:ℝ))^k * (1 + Real.log H)^m
      ≤ (qval μ D g H)^(1/((μ:ℝ)+1)) := by
  have hg1 : (1:ℝ) ≤ 1 + (g:ℝ) := one_le_one_add_g g
  have hH1 : (1:ℝ) ≤ 1 + Real.log H := one_le_one_add_log H
  have hg0 : (0:ℝ) ≤ 1 + (g:ℝ) := le_trans zero_le_one hg1
  have hH0 : (0:ℝ) ≤ 1 + Real.log H := le_trans zero_le_one hH1
  have hμ0 : (0:ℝ) ≤ (μ:ℝ)+2 := by linarith [nat_cast_nonneg_R μ]
  have hbase : (0:ℝ) ≤ C * (1+(g:ℝ))^k * (1+Real.log H)^m :=
    mul_nonneg (mul_nonneg hC0 (pow_nonneg hg0 _)) (pow_nonneg hH0 _)
  apply rpow_ge_of_pow_le μ hbase
  have hpow : (C * (1+(g:ℝ))^k * (1+Real.log H)^m)^(μ+1)
      = C^(μ+1) * (1+(g:ℝ))^(k*(μ+1)) * (1+Real.log H)^(m*(μ+1)) := by
    rw [mul_pow, mul_pow, pow_mul, pow_mul]
  rw [hpow]
  have hCμ : C^(μ+1) ≤ ((μ:ℝ)+2)^(100*(μ+1)^2) := by
    calc C^(μ+1) ≤ (((μ:ℝ)+2)^(100*(μ+1)))^(μ+1) := pow_le_pow_left₀ hC0 hC (μ+1)
      _ = ((μ:ℝ)+2)^((100*(μ+1))*(μ+1)) := (pow_mul _ _ _).symm
      _ = ((μ:ℝ)+2)^(100*(μ+1)^2) := by congr 1; ring
  have hkE : k*(μ+1) ≤ Ec μ := by
    rw [Ec]
    calc k*(μ+1) ≤ (1000*(μ+1)^3)*(μ+1) := Nat.mul_le_mul_right _ hk
      _ = 1000*(μ+1)^4 := by ring
  have hmF : m*(μ+1) ≤ Fc μ := by
    rw [Fc]
    calc m*(μ+1) ≤ (1000*(μ+1)^3)*(μ+1) := Nat.mul_le_mul_right _ hm
      _ = 1000*(μ+1)^4 := by ring
  have h1 : (1+(g:ℝ))^(k*(μ+1)) ≤ (1+(g:ℝ))^(Ec μ) := pow_le_pow_right₀ hg1 hkE
  have h2 : (1+Real.log H)^(m*(μ+1)) ≤ (1+Real.log H)^(Fc μ) := pow_le_pow_right₀ hH1 hmF
  have h3 : C^(μ+1) * (1+(g:ℝ))^(k*(μ+1)) ≤ ((μ:ℝ)+2)^(100*(μ+1)^2) * (1+(g:ℝ))^(Ec μ) :=
    mul_le_mul hCμ h1 (pow_nonneg hg0 _) (pow_nonneg hμ0 _)
  have h4 : C^(μ+1) * (1+(g:ℝ))^(k*(μ+1)) * (1+Real.log H)^(m*(μ+1))
      ≤ ((μ:ℝ)+2)^(100*(μ+1)^2) * (1+(g:ℝ))^(Ec μ) * (1+Real.log H)^(Fc μ) :=
    mul_le_mul h3 h2 (pow_nonneg hH0 _)
      (mul_nonneg (pow_nonneg hμ0 _) (pow_nonneg hg0 _))
  calc C^(μ+1) * (1+(g:ℝ))^(k*(μ+1)) * (1+Real.log H)^(m*(μ+1))
      ≤ ((μ:ℝ)+2)^(100*(μ+1)^2) * (1+(g:ℝ))^(Ec μ) * (1+Real.log H)^(Fc μ) := h4
    _ = (CCc μ : ℝ) * (1+(g:ℝ))^(Ec μ) * (1+Real.log H)^(Fc μ) := by
        rw [pow_eq_CCc μ]
    _ ≤ qval μ D g H := qval_ge_main μ D g H

/-! ## The degree bound in `qval`-power form -/

lemma factorial_rpow_le (μ : ℕ) :
    ((((μ+1).factorial : ℕ) : ℝ)) ^ (1/((μ:ℝ)+1)) ≤ (μ:ℝ)+1 := by
  have hp0 : (0:ℝ) < (μ:ℝ)+1 := by linarith [nat_cast_nonneg_R μ]
  have hfac0 : (0:ℝ) ≤ (((μ+1).factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfact_nat : (μ+1).factorial ≤ (μ+1)^(μ+1) := Nat.factorial_le_pow (μ+1)
  have hfact : (((μ+1).factorial : ℕ) : ℝ) ≤ ((μ:ℝ)+1)^(μ+1) := by
    have h2 : (((μ+1).factorial : ℕ) : ℝ) ≤ (((μ+1)^(μ+1) : ℕ) : ℝ) := by
      exact_mod_cast hfact_nat
    have h3 : ((((μ+1)^(μ+1) : ℕ)) : ℝ) = ((μ:ℝ)+1)^(μ+1) := by push_cast; ring
    linarith [h2, h3.le, h3.ge]
  calc ((((μ+1).factorial : ℕ) : ℝ)) ^ (1/((μ:ℝ)+1))
      ≤ (((μ:ℝ)+1)^(μ+1))^(1/((μ:ℝ)+1)) := Real.rpow_le_rpow hfac0 hfact (one_div_pos.mpr hp0).le
    _ = ((μ:ℝ)+1)^((((μ+1 : ℕ)) : ℝ) * (1/((μ:ℝ)+1))) := by
        rw [← Real.rpow_natCast ((μ:ℝ)+1) (μ+1), ← Real.rpow_mul (le_of_lt hp0)]
    _ = (μ:ℝ)+1 := by
        have hc : (((μ+1 : ℕ)) : ℝ) * (1/((μ:ℝ)+1)) = 1 := by
          push_cast; field_simp
        rw [hc, Real.rpow_one]

lemma nine_add_eight_rpow_le (μ g : ℕ) :
    (8*(g:ℝ)+9) ^ (1/((μ:ℝ)+1)) ≤ 9 * (1+(g:ℝ)) := by
  have hp0 : (0:ℝ) < (μ:ℝ)+1 := by linarith [nat_cast_nonneg_R μ]
  have hg0 : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g
  have hle : (1:ℝ)/((μ:ℝ)+1) ≤ 1 := by
    rw [div_le_one hp0]; linarith
  have hbase : 8*(g:ℝ)+9 ≤ 9*(1+(g:ℝ)) := by linarith
  have hb1a : (0:ℝ) ≤ 8*(g:ℝ)+9 := by linarith
  have hb2a : (0:ℝ) ≤ 9*(1+(g:ℝ)) := by linarith
  have h9 : (9:ℝ)^(1/((μ:ℝ)+1)) ≤ 9 := by
    have h : (9:ℝ)^(1/((μ:ℝ)+1)) ≤ (9:ℝ)^(1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    simpa using h
  have h1g : (1:ℝ) ≤ 1+(g:ℝ) := by linarith
  have hg : (1+(g:ℝ))^(1/((μ:ℝ)+1)) ≤ 1+(g:ℝ) := by
    have h : (1+(g:ℝ))^(1/((μ:ℝ)+1)) ≤ (1+(g:ℝ))^(1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1g hle
    simpa using h
  have h5 : (0:ℝ) ≤ (1+(g:ℝ))^(1/((μ:ℝ)+1)) := Real.rpow_nonneg (by linarith) _
  calc (8*(g:ℝ)+9)^(1/((μ:ℝ)+1)) ≤ (9*(1+(g:ℝ)))^(1/((μ:ℝ)+1)) :=
        Real.rpow_le_rpow hb1a hbase (one_div_pos.mpr hp0).le
    _ = (9:ℝ)^(1/((μ:ℝ)+1)) * (1+(g:ℝ))^(1/((μ:ℝ)+1)) := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ 9 * (1+(g:ℝ)) := mul_le_mul h9 hg h5 (by norm_num)

lemma dV_le_qval_rpow_aux (μ D g H : ℕ) (hH : 1 ≤ H)
    (hb : ((bV μ g H : ℕ) : ℝ) ≤ qval μ D g H)
    (hd : ((dV μ g (bV μ g H) : ℕ) : ℝ) ≤
      8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        (((bV μ g H : ℕ) : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1))) :
    ((dV μ g (bV μ g H) : ℕ) : ℝ) ≤ 408 * ((μ : ℝ) + 1) * (1 + (g : ℝ)) *
        (qval μ D g H) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) := by
  have hp0 : (0:ℝ) < (μ:ℝ)+1 := by linarith [nat_cast_nonneg_R μ]
  have hM1 : (1:ℝ) ≤ qval μ D g H := one_le_qval μ D g H hH
  have hM0 : (0:ℝ) ≤ qval μ D g H := le_of_lt (lt_of_lt_of_le zero_lt_one hM1)
  have hg0 : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g
  have hb1 : (1:ℝ) ≤ ((bV μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_bV μ g H
  have hb2M : ((bV μ g H : ℕ) : ℝ) + 2 ≤ 3 * qval μ D g H := by linarith
  have hbp : (((bV μ g H : ℕ) : ℝ) + 2) ^ ((μ:ℝ)/((μ:ℝ)+1))
      ≤ 3 * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := by
    have h2a : (((bV μ g H : ℕ) : ℝ) + 2)^((μ:ℝ)/((μ:ℝ)+1))
        ≤ (3*qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) :=
      Real.rpow_le_rpow (by linarith) hb2M (div_nonneg (nat_cast_nonneg_R μ) (by linarith))
    rw [Real.mul_rpow (by norm_num) hM0] at h2a
    have hμp : (μ:ℝ)/((μ:ℝ)+1) ≤ 1 := by
      rw [div_le_one hp0]; linarith [nat_cast_nonneg_R μ]
    have h3 : (3:ℝ)^((μ:ℝ)/((μ:ℝ)+1)) ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hμp
      simpa using h
    calc (((bV μ g H : ℕ) : ℝ) + 2)^((μ:ℝ)/((μ:ℝ)+1))
        ≤ (3:ℝ)^((μ:ℝ)/((μ:ℝ)+1)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := h2a
      _ ≤ 3 * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hM0 _)
  have hDf : ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1/((μ:ℝ)+1))
      ≤ ((μ:ℝ)+1) * (9 * (1+(g:ℝ))) := by
    rw [Real.mul_rpow (Nat.cast_nonneg _) (by linarith)]
    exact mul_le_mul (factorial_rpow_le μ) (nine_add_eight_rpow_le μ g)
      (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hd' : ((dV μ g (bV μ g H) : ℕ) : ℝ)
      ≤ 8 * (((μ:ℝ)+1) * (9 * (1+(g:ℝ)))) * (3 * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) := by
    calc ((dV μ g (bV μ g H) : ℕ) : ℝ)
        ≤ 8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1/((μ:ℝ)+1))
            * (((bV μ g H : ℕ) : ℝ) + 2) ^ ((μ:ℝ)/((μ:ℝ)+1)) := hd
      _ ≤ 8 * (((μ:ℝ)+1) * (9 * (1+(g:ℝ))))
            * (3 * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) := by
          have hA1 : (0:ℝ) ≤ (((bV μ g H : ℕ) : ℝ) + 2) ^ ((μ:ℝ)/((μ:ℝ)+1)) :=
            Real.rpow_nonneg (by linarith [nat_cast_nonneg_R (bV μ g H)]) _
          have hC1 : (0:ℝ) ≤ (μ:ℝ)+1 := by linarith [nat_cast_nonneg_R μ]
          have hC2 : (0:ℝ) ≤ 1+(g:ℝ) := by linarith [hg0]
          have hB1 : (0:ℝ) ≤ 8 * (((μ:ℝ)+1) * (9 * (1+(g:ℝ)))) :=
            mul_nonneg (by norm_num) (mul_nonneg hC1 (by linarith))
          exact mul_le_mul (mul_le_mul_of_nonneg_left hDf (by norm_num)) hbp hA1 hB1
  calc ((dV μ g (bV μ g H) : ℕ) : ℝ)
      ≤ 8 * (((μ:ℝ)+1) * (9 * (1+(g:ℝ)))) * (3 * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1))) := hd'
    _ = 216 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := by ring
    _ ≤ 408 * ((μ:ℝ)+1) * (1+(g:ℝ)) * (qval μ D g H)^((μ:ℝ)/((μ:ℝ)+1)) := by
        have hup : (0:ℝ) ≤ (μ:ℝ)+1 := by linarith [nat_cast_nonneg_R μ]
        have hgp : (0:ℝ) ≤ 1+(g:ℝ) := by linarith [hg0]
        have hfin : (216:ℝ) * ((μ:ℝ)+1) * (1+(g:ℝ)) ≤ 408 * ((μ:ℝ)+1) * (1+(g:ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hup) hgp
        exact mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg hM0 _)

/-! ## The logarithm of `1/epsV` -/

lemma log_one_div_epsV_aux (μ g H : ℕ) (hH : 1 ≤ H) :
    Real.log (1 / epsV μ g H) =
      Real.log (4 * ((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
                ((dV μ g (bV μ g H) : ℕ) : ℝ) * ((μ : ℝ) + 1)) +
      (g : ℝ) * Real.log (((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
                ((H : ℝ)) ^ ((((μ + 1) + 1) * dV μ g (bV μ g H) * g))) := by
  have hN : (0:ℝ) < ((N1V μ g H : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_N1V μ g H)
  have hQ : (0:ℝ) < ((QV μ g H : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_QV μ g H)
  have hd : (0:ℝ) < ((dV μ g (bV μ g H) : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_dV μ g (bV μ g H))
  have hm : (0:ℝ) < (μ:ℝ)+1 := by linarith [nat_cast_nonneg_R μ]
  have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
  have hYpos : 0 < ((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
      ((H:ℝ) ^ ((((μ + 1) + 1) * dV μ g (bV μ g H) * g))) := by
    have h1 : (0:ℝ) < (H:ℝ)^((((μ + 1) + 1) * dV μ g (bV μ g H) * g)) :=
      lt_of_lt_of_le zero_lt_one (one_le_pow₀ hH1)
    exact mul_pos (mul_pos hN hQ) h1
  have hDpos : 0 < 4 * ((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
      ((dV μ g (bV μ g H) : ℕ) : ℝ) * ((μ : ℝ) + 1) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hN) hQ) hd) hm
  have heps : 1 / epsV μ g H
      = (4 * ((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
          ((dV μ g (bV μ g H) : ℕ) : ℝ) * ((μ : ℝ) + 1))
        * ((((N1V μ g H : ℕ) : ℝ) * ((QV μ g H : ℕ) : ℝ) *
            ((H:ℝ) ^ ((((μ + 1) + 1) * dV μ g (bV μ g H) * g)))) ^ g) := by
    rw [epsV, liou]
    rw [show monoCount (μ + 1) (dV μ g (bV μ g H)) = N1V μ g H from rfl]
    rw [one_div_div, div_eq_mul_inv, one_div, inv_inv]
  rw [heps, Real.log_mul (ne_of_gt hDpos) (ne_of_gt (pow_pos hYpos g)), Real.log_pow]

end Work.WilkiesH.Interp.V2qe
