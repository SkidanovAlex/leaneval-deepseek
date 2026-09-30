import Mathlib
import Submission.Work.BMF.adi_const

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.consts_le_C1c`

The final constant `C1c k C₀ = (C₀+2)^(Eexp k)` of the ADI assembly dominates all the
auxiliary constants `Cgs`, `CTc`, `Ceps1`, `Ceps2`, `C2c` appearing in the descent.

Everything rests on the single numerical estimate `1 + Dgrow k C₀ ≤ (C₀+2)^(4(k+1)²+8)`,
from which `CTc` and then all the other constants are bounded by explicit powers of `C₀+2`;
the exponents involved are `O(k³)` while `Eexp` is `≥ 200(k+1)⁴+100`.
-/

namespace Work.BMF

open Polynomial Finset

set_option maxRecDepth 10000

/-! ### Elementary helpers -/

/-- `a * b ≤ A^{m+n}` from `a ≤ A^m`, `b ≤ A^n`, `0 ≤ b` and `1 ≤ A`. -/
private lemma mul_le_pow {A a b : ℝ} {m n : ℕ} (hA : 1 ≤ A) (hb0 : 0 ≤ b)
    (ha : a ≤ A ^ m) (hb : b ≤ A ^ n) : a * b ≤ A ^ (m + n) := by
  have hAm : (0 : ℝ) ≤ A ^ m := pow_nonneg (le_trans zero_le_one hA) m
  calc a * b ≤ A ^ m * b := mul_le_mul_of_nonneg_right ha hb0
    _ ≤ A ^ m * A ^ n := mul_le_mul_of_nonneg_left hb hAm
    _ = A ^ (m + n) := (pow_add A m n).symm

/-- `a + b ≤ A^{n+1}` from `a, b ≤ A^n` and `2 ≤ A`. -/
private lemma add_le_pow {A a b : ℝ} {n : ℕ} (hA : 2 ≤ A) (ha : a ≤ A ^ n) (hb : b ≤ A ^ n) :
    a + b ≤ A ^ (n + 1) := by
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hAn : (0 : ℝ) ≤ A ^ n := pow_nonneg hA0 n
  calc a + b ≤ A ^ n + A ^ n := add_le_add ha hb
    _ = 2 * A ^ n := by ring
    _ ≤ A * A ^ n := by nlinarith [hAn]
    _ = A ^ (n + 1) := by rw [pow_succ]; ring

/-- `a + b + c ≤ A^{n+2}` from `a, b, c ≤ A^n` and `2 ≤ A`. -/
private lemma three_le_pow {A a b c : ℝ} {n : ℕ} (hA : 2 ≤ A)
    (ha : a ≤ A ^ n) (hb : b ≤ A ^ n) (hc : c ≤ A ^ n) : a + b + c ≤ A ^ (n + 2) := by
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hcn : A ^ n ≤ A ^ (n + 1) := pow_le_pow_right₀ hA1 (Nat.le_succ n)
  have h1 : a + b ≤ A ^ (n + 1) := add_le_pow hA ha hb
  have h2 : a + b + c ≤ A ^ ((n + 1) + 1) := add_le_pow hA h1 (le_trans hc hcn)
  have h3 : (n + 1) + 1 = n + 2 := by omega
  rwa [h3] at h2

/-- `k ≤ (C₀+2)^k`. -/
private lemma natCast_le_pow {k : ℕ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : (k : ℝ) ≤ (C₀ + 2) ^ k := by
  have h2 : (2 : ℝ) ≤ C₀ + 2 := by linarith
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (le_of_lt (Nat.lt_two_pow_self (n := k)))
  have h3 : (2 : ℝ) ^ k ≤ (C₀ + 2) ^ k := pow_le_pow_left₀ (by norm_num) h2 k
  linarith

/-- `k + 1 ≤ (C₀+2)^{k+1}`. -/
private lemma succ_le_pow {k : ℕ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    (k : ℝ) + 1 ≤ (C₀ + 2) ^ (k + 1) := by
  have h2 : (2 : ℝ) ≤ C₀ + 2 := by linarith
  have hk : ((k : ℝ) + 1) ≤ (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast (le_of_lt (Nat.lt_two_pow_self (n := k + 1)))
  have h3 : (2 : ℝ) ^ (k + 1) ≤ (C₀ + 2) ^ (k + 1) :=
    pow_le_pow_left₀ (by norm_num) h2 (k + 1)
  linarith

/-- `k^k ≤ (C₀+2)^{k²}`. -/
private lemma selfPow_le_pow {k : ℕ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    (k : ℝ) ^ k ≤ (C₀ + 2) ^ (k * k) := by
  have h2 : (2 : ℝ) ≤ C₀ + 2 := by linarith
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (le_of_lt (Nat.lt_two_pow_self (n := k)))
  have h3 : ((k : ℝ)) ^ k ≤ ((2 : ℝ) ^ k) ^ k := pow_le_pow_left₀ (by positivity) hk k
  rw [← pow_mul] at h3
  have h4 : (2 : ℝ) ^ (k * k) ≤ (C₀ + 2) ^ (k * k) :=
    pow_le_pow_left₀ (by norm_num) h2 (k * k)
  linarith

/-- `2π ≤ (C₀+2)²`. -/
private lemma twoPi_le_pow {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 2 * Real.pi ≤ (C₀ + 2) ^ 2 := by
  have h3 : (3 : ℝ) ≤ C₀ + 2 := by linarith
  have hp : 2 * Real.pi < 9 := by linarith [Real.pi_lt_four]
  have h4 : (3 : ℝ) ^ 2 ≤ (C₀ + 2) ^ 2 := pow_le_pow_left₀ (by norm_num) h3 2
  norm_num at h4
  linarith

/-- `4 ≤ (C₀+2)²`. -/
private lemma four_le_pow {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : (4 : ℝ) ≤ (C₀ + 2) ^ 2 := by
  have h3 : (3 : ℝ) ≤ C₀ + 2 := by linarith
  nlinarith [sq_nonneg (C₀ + 2)]

/-- `1 ≤ C₀+2`. -/
private lemma one_le_C0p2 {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : (1 : ℝ) ≤ C₀ + 2 := by linarith

/-- `2 ≤ C₀+2`. -/
private lemma two_le_C0p2 {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : (2 : ℝ) ≤ C₀ + 2 := by linarith

/-- `3 ≤ C₀+2`. -/
private lemma three_le_C0p2 {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : (3 : ℝ) ≤ C₀ + 2 := by linarith

private lemma CT1_nonneg (k : ℕ) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 0 ≤ CT1 k C₀ := by
  rw [CT1]; positivity

/-- Nonnegativity of `CTc`. -/
private lemma CTc_nonneg (k : ℕ) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 0 ≤ CTc k C₀ := by
  have hD : (0 : ℝ) ≤ Dgrow k C₀ := by rw [Dgrow]; positivity
  rw [CTc, Alev, CT1]; simp only [Nat.sub_zero, Nat.cast_zero, sub_zero]; positivity

/-- Nonnegativity of `Ceps1`. -/
private lemma Ceps1_nonneg (k : ℕ) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 0 ≤ Ceps1 k C₀ := by
  have h0 : (0 : ℝ) ≤ CTc k C₀ := CTc_nonneg k hC₀
  rw [Ceps1]; positivity

/-- Nonnegativity of `Ceps2`. -/
private lemma Ceps2_nonneg (k : ℕ) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 0 ≤ Ceps2 k C₀ := by
  have h0 : (0 : ℝ) ≤ CTc k C₀ := CTc_nonneg k hC₀
  rw [Ceps2]; positivity

/-- Nonnegativity of `C2c`. -/
private lemma C2c_nonneg (k : ℕ) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 0 ≤ C2c k C₀ := by
  have h1 : (0 : ℝ) ≤ Ceps1 k C₀ := Ceps1_nonneg k hC₀
  have h2 : (0 : ℝ) ≤ Ceps2 k C₀ := Ceps2_nonneg k hC₀
  rw [C2c]; positivity

/-- Nonnegativity of `Cgs`. -/
private lemma Cgs_nonneg (k : ℕ) {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 0 ≤ Cgs k C₀ := by
  have h1 : (0 : ℝ) ≤ CTc k C₀ := CTc_nonneg k hC₀
  have h2 : (0 : ℝ) ≤ C2c k C₀ := C2c_nonneg k hC₀
  rw [Cgs]; positivity

/-- The exponent of the bound for `CTc`. -/
private def Erem (k : ℕ) : ℕ := 4 * (k + 1) ^ 3 + k ^ 2 + 13 * k + 17

/-- **Step 1.** `1 + Dgrow k C₀` is below a fixed power of `C₀+2`. -/
private lemma dgrow_le_pow_aux (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    1 + Dgrow k C₀ ≤ (C₀ + 2) ^ (4 * (k + 1) ^ 2 + 8) := by
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := one_le_C0p2 hC₀
  have hA2 : (2 : ℝ) ≤ C₀ + 2 := two_le_C0p2 hC₀
  have hA3 : (3 : ℝ) ≤ C₀ + 2 := three_le_C0p2 hC₀
  have hC00 : (0 : ℝ) ≤ C₀ := by linarith
  have e_k : (k : ℝ) ≤ (C₀ + 2) ^ k := natCast_le_pow hC₀
  have e_k1 : (k : ℝ) + 1 ≤ (C₀ + 2) ^ (k + 1) := succ_le_pow hC₀
  have e_kk : (k : ℝ) ^ k ≤ (C₀ + 2) ^ (k * k) := selfPow_le_pow hC₀
  have e_C2 : C₀ ^ 2 ≤ (C₀ + 2) ^ 2 := pow_le_pow_left₀ hC00 (by linarith) 2
  have e_three : (3 : ℝ) ^ (k + 1) ≤ (C₀ + 2) ^ (k + 1) :=
    pow_le_pow_left₀ (by norm_num) hA3 (k + 1)
  have e_C0 : C₀ ^ (2 * k + 2) ≤ (C₀ + 2) ^ (2 * k + 2) :=
    pow_le_pow_left₀ hC00 (by linarith) (2 * k + 2)
  have e_4 : (4 : ℝ) ≤ (C₀ + 2) ^ 2 := four_le_pow hC₀
  have ea : (4 : ℝ) * 3 ^ (k + 1) ≤ (C₀ + 2) ^ (2 + (k + 1)) :=
    mul_le_pow hA1 (by positivity) e_4 e_three
  have eb : (4 * 3 ^ (k + 1)) * C₀ ^ (2 * k + 2) ≤ (C₀ + 2) ^ ((2 + (k + 1)) + (2 * k + 2)) :=
    mul_le_pow hA1 (by positivity) ea e_C0
  have e_last : (4 : ℝ) * (3 ^ (k + 1) * C₀ ^ (2 * k + 2)) ≤
      (C₀ + 2) ^ (2 + (k + 1) + (2 * k + 2)) := by
    rw [show (4 : ℝ) * (3 ^ (k + 1) * C₀ ^ (2 * k + 2)) =
      (4 * 3 ^ (k + 1)) * C₀ ^ (2 * k + 2) by ring]
    exact eb
  have hY1 : (1 : ℝ) ≤ 3 ^ (k + 1) * C₀ ^ (2 * k + 2) := by
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ C₀ ^ (2 * k + 2) := one_le_pow₀ hC₀
    nlinarith
  have hY2 : 2 * (1 + 3 ^ (k + 1) * C₀ ^ (2 * k + 2)) ≤ 4 * (3 ^ (k + 1) * C₀ ^ (2 * k + 2)) := by
    linarith
  have hP0 : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * C₀ ^ 2 := by positivity
  have hD : Dgrow k C₀ ≤ (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * C₀ ^ 2 *
      (4 * (3 ^ (k + 1) * C₀ ^ (2 * k + 2))) := by
    rw [Dgrow]
    exact mul_le_mul_of_nonneg_left hY2 hP0
  have h1 : (k : ℝ) * ((k : ℝ) + 1) ≤ (C₀ + 2) ^ (k + (k + 1)) :=
    mul_le_pow hA1 (by positivity) e_k e_k1
  have h2 : (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k ≤ (C₀ + 2) ^ ((k + (k + 1)) + (k * k)) :=
    mul_le_pow hA1 (by positivity) h1 e_kk
  have h3 : (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * C₀ ^ 2 ≤
      (C₀ + 2) ^ (((k + (k + 1)) + (k * k)) + 2) :=
    mul_le_pow hA1 (by positivity) h2 e_C2
  have h4 : (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * C₀ ^ 2 *
      (4 * (3 ^ (k + 1) * C₀ ^ (2 * k + 2))) ≤
      (C₀ + 2) ^ ((((k + (k + 1)) + (k * k)) + 2) + (2 + (k + 1) + (2 * k + 2))) :=
    mul_le_pow hA1 (by positivity) h3 e_last
  have hone : (1 : ℝ) ≤ (C₀ + 2) ^ ((((k + (k + 1)) + (k * k)) + 2) +
      (2 + (k + 1) + (2 * k + 2))) := one_le_pow₀ hA1
  have hsum : 1 + (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * C₀ ^ 2 *
      (4 * (3 ^ (k + 1) * C₀ ^ (2 * k + 2))) ≤
      (C₀ + 2) ^ ((((k + (k + 1)) + (k * k)) + 2) + (2 + (k + 1) + (2 * k + 2)) + 1) :=
    add_le_pow hA2 hone h4
  have hexp : ((((k + (k + 1)) + (k * k)) + 2) + (2 + (k + 1) + (2 * k + 2)) + 1) ≤
      4 * (k + 1) ^ 2 + 8 := by nlinarith
  calc 1 + Dgrow k C₀ ≤ 1 + (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * C₀ ^ 2 *
        (4 * (3 ^ (k + 1) * C₀ ^ (2 * k + 2))) := by linarith
    _ ≤ (C₀ + 2) ^ ((((k + (k + 1)) + (k * k)) + 2) + (2 + (k + 1) + (2 * k + 2)) + 1) := hsum
    _ ≤ (C₀ + 2) ^ (4 * (k + 1) ^ 2 + 8) := pow_le_pow_right₀ hA1 hexp

/-- **Step 2.** `CTc k C₀ ≤ (C₀+2)^{Erem k}`. -/
private lemma CTc_le_pow_aux (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    CTc k C₀ ≤ (C₀ + 2) ^ (Erem k) := by
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := one_le_C0p2 hC₀
  have hC00 : (0 : ℝ) ≤ C₀ := by linarith
  have hDg0 : (0 : ℝ) ≤ Dgrow k C₀ := by rw [Dgrow]; positivity
  have hDg : 1 + Dgrow k C₀ ≤ (C₀ + 2) ^ (4 * (k + 1) ^ 2 + 8) := dgrow_le_pow_aux k C₀ hC₀
  have e_k2 : ((k : ℝ) + 2) ≤ (C₀ + 2) ^ (k + 2) := by
    have h : ((k + 2 : ℕ) : ℝ) ≤ (C₀ + 2) ^ (k + 2) := natCast_le_pow (C₀ := C₀) (k := k + 2) hC₀
    push_cast at h
    exact h
  have hfac1 : C₀ + (k : ℝ) + 2 ≤ (C₀ + 2) ^ ((k + 2) + 1) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : C₀ + (k : ℝ) + 2 ≤ (C₀ + 2) * ((k : ℝ) + 2) := by
      nlinarith [hC₀, hk0]
    calc C₀ + (k : ℝ) + 2 ≤ (C₀ + 2) * ((k : ℝ) + 2) := h1
      _ ≤ (C₀ + 2) * (C₀ + 2) ^ (k + 2) := mul_le_mul_of_nonneg_left e_k2 (by linarith)
      _ = (C₀ + 2) ^ ((k + 2) + 1) := (pow_succ' (C₀ + 2) (k + 2)).symm
  have hpow : (1 + Dgrow k C₀) ^ (k + 1) ≤ (C₀ + 2) ^ ((4 * (k + 1) ^ 2 + 8) * (k + 1)) := by
    calc (1 + Dgrow k C₀) ^ (k + 1) ≤ ((C₀ + 2) ^ (4 * (k + 1) ^ 2 + 8)) ^ (k + 1) :=
          pow_le_pow_left₀ (by linarith) hDg (k + 1)
      _ = (C₀ + 2) ^ ((4 * (k + 1) ^ 2 + 8) * (k + 1)) := by rw [pow_mul]
  have hAl1 : (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1) ≤
      (C₀ + 2) ^ ((k + 2) + 1 + ((4 * (k + 1) ^ 2 + 8) * (k + 1))) :=
    mul_le_pow hA1 (by positivity) hfac1 hpow
  have hAlev : Alev k C₀ 0 ≤ (C₀ + 2) ^ (((k + 2) + 1 + ((4 * (k + 1) ^ 2 + 8) * (k + 1))) +
      (k + 2)) := by
    rw [show Alev k C₀ 0 =
      (C₀ + (k : ℝ) + 2) * (1 + Dgrow k C₀) ^ (k + 1) * ((k : ℝ) + 2) from by simp [Alev]]
    exact mul_le_pow hA1 (by positivity) hAl1 e_k2
  have t1 : 2 * Real.pi ≤ (C₀ + 2) ^ 2 := twoPi_le_pow hC₀
  have t2 : (k : ℝ) ≤ (C₀ + 2) ^ k := natCast_le_pow hC₀
  have t3 : (k : ℝ) + 1 ≤ (C₀ + 2) ^ (k + 1) := succ_le_pow hC₀
  have t4 : (k : ℝ) ^ k ≤ (C₀ + 2) ^ (k * k) := selfPow_le_pow hC₀
  have t5 : C₀ ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; linarith
  have c1 : 2 * Real.pi * (k : ℝ) ≤ (C₀ + 2) ^ (2 + k) := mul_le_pow hA1 (by positivity) t1 t2
  have c2 : 2 * Real.pi * (k : ℝ) * ((k : ℝ) + 1) ≤ (C₀ + 2) ^ ((2 + k) + (k + 1)) :=
    mul_le_pow hA1 (by positivity) c1 t3
  have c3 : 2 * Real.pi * (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k ≤
      (C₀ + 2) ^ (((2 + k) + (k + 1)) + (k * k)) := mul_le_pow hA1 (by positivity) c2 t4
  have hCT1 : CT1 k C₀ ≤ (C₀ + 2) ^ ((((2 + k) + (k + 1)) + (k * k)) + 1) := by
    rw [show CT1 k C₀ = 2 * Real.pi * (k : ℝ) * ((k : ℝ) + 1) * (k : ℝ) ^ k * C₀ from rfl]
    exact mul_le_pow hA1 (by positivity) c3 t5
  have hC0k : C₀ ^ k ≤ (C₀ + 2) ^ k := pow_le_pow_left₀ hC00 (by linarith) k
  have d1 : Alev k C₀ 0 * CT1 k C₀ ≤
      (C₀ + 2) ^ ((((k + 2) + 1 + ((4 * (k + 1) ^ 2 + 8) * (k + 1))) + (k + 2)) +
        ((((2 + k) + (k + 1)) + (k * k)) + 1)) :=
    mul_le_pow hA1 (CT1_nonneg k hC₀) hAlev hCT1
  have d2 : Alev k C₀ 0 * CT1 k C₀ * C₀ ^ k ≤
      (C₀ + 2) ^ (((((k + 2) + 1 + ((4 * (k + 1) ^ 2 + 8) * (k + 1))) + (k + 2)) +
        ((((2 + k) + (k + 1)) + (k * k)) + 1)) + k) :=
    mul_le_pow hA1 (by positivity) d1 hC0k
  have hCTc : CTc k C₀ ≤
      (C₀ + 2) ^ (((((k + 2) + 1 + ((4 * (k + 1) ^ 2 + 8) * (k + 1))) + (k + 2)) +
        ((((2 + k) + (k + 1)) + (k * k)) + 1)) + k) := by
    rw [show CTc k C₀ = Alev k C₀ 0 * CT1 k C₀ * C₀ ^ k from rfl]
    exact d2
  have hexp : (((((k + 2) + 1 + ((4 * (k + 1) ^ 2 + 8) * (k + 1))) + (k + 2)) +
      ((((2 + k) + (k + 1)) + (k * k)) + 1)) + k) ≤ Erem k := by
    rw [Erem]; nlinarith
  exact le_trans hCTc (pow_le_pow_right₀ hA1 hexp)

/-- **Step 3.** The third summand of `C2c`. -/
private lemma C2c_third_le_pow (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    2 * ((k : ℝ) + 1) ^ (2 * k + 4) * C₀ ≤ (C₀ + 2) ^ ((k + 1) * (2 * k + 4) + 2) := by
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := one_le_C0p2 hC₀
  have e_k1 : (k : ℝ) + 1 ≤ (C₀ + 2) ^ (k + 1) := succ_le_pow hC₀
  have e_pow : ((k : ℝ) + 1) ^ (2 * k + 4) ≤ (C₀ + 2) ^ ((k + 1) * (2 * k + 4)) := by
    calc ((k : ℝ) + 1) ^ (2 * k + 4) ≤ ((C₀ + 2) ^ (k + 1)) ^ (2 * k + 4) :=
          pow_le_pow_left₀ (by positivity) e_k1 (2 * k + 4)
      _ = (C₀ + 2) ^ ((k + 1) * (2 * k + 4)) := by rw [pow_mul]
  have e_2 : (2 : ℝ) ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; exact two_le_C0p2 hC₀
  have e_C0 : C₀ ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; linarith
  have s1 : 2 * ((k : ℝ) + 1) ^ (2 * k + 4) ≤ (C₀ + 2) ^ (1 + (k + 1) * (2 * k + 4)) :=
    mul_le_pow hA1 (by positivity) e_2 e_pow
  have s2 : 2 * ((k : ℝ) + 1) ^ (2 * k + 4) * C₀ ≤
      (C₀ + 2) ^ ((1 + (k + 1) * (2 * k + 4)) + 1) :=
    mul_le_pow hA1 (by linarith) s1 e_C0
  exact le_trans s2 (pow_le_pow_right₀ hA1 (by omega))

/-- Bound for `Ceps1` in terms of `Erem`. -/
private lemma Ceps1_le_Erem (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    Ceps1 k C₀ ≤ (C₀ + 2) ^ (Erem k + 2 * k + 2) := by
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := one_le_C0p2 hC₀
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h0 : (0 : ℝ) ≤ CTc k C₀ := CTc_nonneg k hC₀
  have hnum : (0 : ℝ) ≤ ((k : ℝ) + 1) * CTc k C₀ * C₀ ^ (k + 1) :=
    mul_nonneg (mul_nonneg (by positivity) h0) (by positivity)
  have s1 : Ceps1 k C₀ ≤ ((k : ℝ) + 1) * CTc k C₀ * C₀ ^ (k + 1) := by
    rw [Ceps1]
    exact div_le_self hnum hpi
  have e_pow : C₀ ^ (k + 1) ≤ (C₀ + 2) ^ (k + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) (k + 1)
  have e_k1 : ((k : ℝ) + 1) ≤ (C₀ + 2) ^ (k + 1) := succ_le_pow hC₀
  have t1 : ((k : ℝ) + 1) * C₀ ^ (k + 1) ≤ (C₀ + 2) ^ ((k + 1) + (k + 1)) :=
    mul_le_pow hA1 (by positivity) e_k1 e_pow
  have t2 : ((k : ℝ) + 1) * C₀ ^ (k + 1) * CTc k C₀ ≤
      (C₀ + 2) ^ (((k + 1) + (k + 1)) + Erem k) :=
    mul_le_pow hA1 h0 t1 (CTc_le_pow_aux k C₀ hC₀)
  have s2 : ((k : ℝ) + 1) * CTc k C₀ * C₀ ^ (k + 1) ≤ (C₀ + 2) ^ (Erem k + 2 * k + 2) := by
    rw [show ((k : ℝ) + 1) * CTc k C₀ * C₀ ^ (k + 1) =
      (((k : ℝ) + 1) * C₀ ^ (k + 1)) * CTc k C₀ by ring]
    exact le_trans t2 (pow_le_pow_right₀ hA1 (by rw [Erem]; omega))
  exact le_trans s1 s2

/-- Bound for `Ceps2` in terms of `Erem`. -/
private lemma Ceps2_le_Erem (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    Ceps2 k C₀ ≤ (C₀ + 2) ^ (Erem k + 5 * k + 2) := by
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := one_le_C0p2 hC₀
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h0 : (0 : ℝ) ≤ CTc k C₀ := CTc_nonneg k hC₀
  have hnum : (0 : ℝ) ≤ ((k : ℝ) + 1) * CTc k C₀ * C₀ * (3 * C₀ ^ 3) ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) h0) (by linarith)) (by positivity)
  have s1 : Ceps2 k C₀ ≤ ((k : ℝ) + 1) * CTc k C₀ * C₀ * (3 * C₀ ^ 3) ^ k := by
    rw [Ceps2]
    exact div_le_self hnum hpi
  have h3C : 3 * C₀ ^ 3 ≤ (C₀ + 2) ^ 4 := by
    have e3 : (3 : ℝ) ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; exact three_le_C0p2 hC₀
    have eC : C₀ ^ 3 ≤ (C₀ + 2) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have h := mul_le_pow hA1 (by positivity) e3 eC
    rwa [show (1 : ℕ) + 3 = 4 from rfl] at h
  have e4k : (3 * C₀ ^ 3) ^ k ≤ (C₀ + 2) ^ (4 * k) := by
    calc (3 * C₀ ^ 3) ^ k ≤ ((C₀ + 2) ^ 4) ^ k := pow_le_pow_left₀ (by positivity) h3C k
      _ = (C₀ + 2) ^ (4 * k) := by rw [pow_mul]
  have e_C0 : C₀ ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; linarith
  have e1 : ((k : ℝ) + 1) * C₀ ≤ (C₀ + 2) ^ ((k + 1) + 1) :=
    mul_le_pow hA1 (by linarith) (succ_le_pow hC₀) e_C0
  have e3 : ((k : ℝ) + 1) * C₀ * (3 * C₀ ^ 3) ^ k ≤ (C₀ + 2) ^ (((k + 1) + 1) + 4 * k) :=
    mul_le_pow hA1 (by positivity) e1 e4k
  have s2 : ((k : ℝ) + 1) * CTc k C₀ * C₀ * (3 * C₀ ^ 3) ^ k ≤
      (C₀ + 2) ^ (Erem k + 5 * k + 2) := by
    rw [show ((k : ℝ) + 1) * CTc k C₀ * C₀ * (3 * C₀ ^ 3) ^ k =
      (((k : ℝ) + 1) * C₀ * (3 * C₀ ^ 3) ^ k) * CTc k C₀ by ring]
    exact le_trans (mul_le_pow hA1 h0 e3 (CTc_le_pow_aux k C₀ hC₀))
      (pow_le_pow_right₀ hA1 (by rw [Erem]; omega))
  exact le_trans s1 s2

/-- Bound for `C2c` in terms of `Erem`. -/
private lemma C2c_le_Erem (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    C2c k C₀ ≤ (C₀ + 2) ^ (Erem k + 5 * k + 5) := by
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := one_le_C0p2 hC₀
  have hA2 : (2 : ℝ) ≤ C₀ + 2 := two_le_C0p2 hC₀
  have h1 : Ceps1 k C₀ ≤ (C₀ + 2) ^ (Erem k + 5 * k + 3) :=
    le_trans (Ceps1_le_Erem k C₀ hC₀) (pow_le_pow_right₀ hA1 (by rw [Erem]; omega))
  have h2 : C₀ * Ceps2 k C₀ ≤ (C₀ + 2) ^ (Erem k + 5 * k + 3) := by
    have eC : C₀ ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; linarith
    have h := mul_le_pow hA1 (Ceps2_nonneg k hC₀) eC (Ceps2_le_Erem k C₀ hC₀)
    rwa [show (1 : ℕ) + (Erem k + 5 * k + 2) = Erem k + 5 * k + 3 from by omega] at h
  have h3 : 2 * ((k : ℝ) + 1) ^ (2 * k + 4) * C₀ ≤ (C₀ + 2) ^ (Erem k + 5 * k + 3) :=
    le_trans (C2c_third_le_pow k C₀ hC₀) (pow_le_pow_right₀ hA1 (by rw [Erem]; nlinarith))
  have hs : Ceps1 k C₀ + C₀ * Ceps2 k C₀ + 2 * ((k : ℝ) + 1) ^ (2 * k + 4) * C₀ ≤
      (C₀ + 2) ^ ((Erem k + 5 * k + 3) + 2) := three_le_pow hA2 h1 h2 h3
  rw [show C2c k C₀ = Ceps1 k C₀ + C₀ * Ceps2 k C₀ + 2 * ((k : ℝ) + 1) ^ (2 * k + 4) * C₀
    from rfl]
  exact le_trans hs (pow_le_pow_right₀ hA1 (by omega))

/-- Bound for the first summand of `Cgs`. -/
private lemma Cgs1_le_Erem (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ / (2 * Real.pi) ≤ (C₀ + 2) ^ (Erem k + k + 3) := by
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := one_le_C0p2 hC₀
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h0 : (0 : ℝ) ≤ CTc k C₀ := CTc_nonneg k hC₀
  have hnum : (0 : ℝ) ≤ 2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) h0) (by linarith)
  have s1 : 2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ / (2 * Real.pi) ≤
      2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ := div_le_self hnum hpi
  have e2 : (2 : ℝ) ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; exact two_le_C0p2 hC₀
  have e_k1 : ((k : ℝ) + 1) ≤ (C₀ + 2) ^ (k + 1) := succ_le_pow hC₀
  have e_C0 : C₀ ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; linarith
  have t1 : 2 * ((k : ℝ) + 1) * C₀ ≤ (C₀ + 2) ^ ((1 + (k + 1)) + 1) :=
    mul_le_pow hA1 (by linarith) (mul_le_pow hA1 (by positivity) e2 e_k1) e_C0
  have t2 : 2 * ((k : ℝ) + 1) * C₀ * CTc k C₀ ≤
      (C₀ + 2) ^ (((1 + (k + 1)) + 1) + Erem k) :=
    mul_le_pow hA1 h0 t1 (CTc_le_pow_aux k C₀ hC₀)
  have s2 : 2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ ≤ (C₀ + 2) ^ (Erem k + k + 3) := by
    rw [show 2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ =
      (2 * ((k : ℝ) + 1) * C₀) * CTc k C₀ by ring]
    exact le_trans t2 (pow_le_pow_right₀ hA1 (by rw [Erem]; omega))
  exact le_trans s1 s2

/-- Bound for `Cgs` in terms of `Erem`. -/
private lemma Cgs_le_Erem (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    Cgs k C₀ ≤ (C₀ + 2) ^ (Erem k + 5 * k + 6) := by
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := one_le_C0p2 hC₀
  have hA2 : (2 : ℝ) ≤ C₀ + 2 := two_le_C0p2 hC₀
  have h1 : 2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ / (2 * Real.pi) ≤
      (C₀ + 2) ^ (Erem k + 5 * k + 5) :=
    le_trans (Cgs1_le_Erem k C₀ hC₀) (pow_le_pow_right₀ hA1 (by rw [Erem]; omega))
  have h2 : C2c k C₀ ≤ (C₀ + 2) ^ (Erem k + 5 * k + 5) := C2c_le_Erem k C₀ hC₀
  have hs := add_le_pow hA2 h1 h2
  rw [show Cgs k C₀ = 2 * ((k : ℝ) + 1) * CTc k C₀ * C₀ / (2 * Real.pi) + C2c k C₀
    from rfl]
  exact le_trans hs (pow_le_pow_right₀ hA1 (by omega))

/-- The constants of the ADI assembly are all dominated by the final constant `C1c`. -/
theorem consts_le_C1c (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    1 ≤ C1c k C₀ ∧ 2 * Cgs k C₀ ≤ C1c k C₀ ∧ ((k : ℝ) + 1) * CTc k C₀ ≤ C1c k C₀ ∧
    Ceps1 k C₀ ≤ C1c k C₀ ∧ Ceps2 k C₀ ≤ C1c k C₀ ∧ 2 * C₀ ^ 2 * C2c k C₀ ≤ C1c k C₀ := by
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := one_le_C0p2 hC₀
  have hA2 : (2 : ℝ) ≤ C₀ + 2 := two_le_C0p2 hC₀
  have hbudget : Erem k + 5 * k + 8 ≤ Eexp k := by
    have hf : (2 : ℕ) ≤ k.factorial + 1 := by have := Nat.factorial_pos k; omega
    have h1 : Erem k + 5 * k + 8 ≤ 200 * (k + 1) ^ 4 + 100 := by rw [Erem]; nlinarith
    have h2 : 200 * (k + 1) ^ 4 + 100 ≤ 100 * (k + 1) ^ 4 * (k.factorial + 1) + 100 := by
      have h3 : 200 * (k + 1) ^ 4 ≤ 100 * (k + 1) ^ 4 * (k.factorial + 1) := by
        calc 200 * (k + 1) ^ 4 = 100 * (k + 1) ^ 4 * 2 := by ring
          _ ≤ 100 * (k + 1) ^ 4 * (k.factorial + 1) := Nat.mul_le_mul_left _ hf
      omega
    have h4 : Eexp k = 100 * (k + 1) ^ 4 * (k.factorial + 1) + 100 := rfl
    omega
  have hC1c : C1c k C₀ = (C₀ + 2) ^ (Eexp k) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC1c]; exact one_le_pow₀ hA1
  · have h := Cgs_le_Erem k C₀ hC₀
    have e2 : (2 : ℝ) ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; exact hA2
    have h2 : 2 * Cgs k C₀ ≤ (C₀ + 2) ^ (Erem k + 5 * k + 6 + 1) := by
      have hm := mul_le_pow hA1 (Cgs_nonneg k hC₀) e2 h
      rwa [show (1 : ℕ) + (Erem k + 5 * k + 6) = Erem k + 5 * k + 6 + 1 from by omega] at hm
    rw [hC1c]
    exact le_trans h2 (pow_le_pow_right₀ hA1 (by omega))
  · have e_k1 : ((k : ℝ) + 1) ≤ (C₀ + 2) ^ (k + 1) := succ_le_pow hC₀
    have h2 : ((k : ℝ) + 1) * CTc k C₀ ≤ (C₀ + 2) ^ ((k + 1) + Erem k) :=
      mul_le_pow hA1 (CTc_nonneg k hC₀) e_k1 (CTc_le_pow_aux k C₀ hC₀)
    rw [hC1c]
    exact le_trans h2 (pow_le_pow_right₀ hA1 (by omega))
  · have h := Ceps1_le_Erem k C₀ hC₀
    rw [hC1c]
    exact le_trans h (pow_le_pow_right₀ hA1 (by omega))
  · have h := Ceps2_le_Erem k C₀ hC₀
    rw [hC1c]
    exact le_trans h (pow_le_pow_right₀ hA1 (by omega))
  · have eC0 : C₀ ^ 2 ≤ (C₀ + 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have e2 : (2 : ℝ) ≤ (C₀ + 2) ^ 1 := by rw [pow_one]; exact hA2
    have q1 : 2 * C₀ ^ 2 ≤ (C₀ + 2) ^ (1 + 2) := mul_le_pow hA1 (by positivity) e2 eC0
    have q2 : 2 * C₀ ^ 2 * C2c k C₀ ≤ (C₀ + 2) ^ ((1 + 2) + (Erem k + 5 * k + 5)) :=
      mul_le_pow hA1 (C2c_nonneg k hC₀) q1 (C2c_le_Erem k C₀ hC₀)
    rw [hC1c]
    exact le_trans q2 (pow_le_pow_right₀ hA1 (by omega))

end Work.BMF
