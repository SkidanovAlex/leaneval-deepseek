import Mathlib
open Finset

namespace Work.HP.MM2

private lemma zpow_helper (z a : ℝ) (hz : 0 ≤ z) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    z ^ a * z ^ (1 - a) = z := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h]
    by_cases ha : a = 0
    · subst ha; norm_num [Real.rpow_zero, Real.rpow_one]
    · rw [Real.zero_rpow ha, zero_mul]
  · rw [← Real.rpow_add h, show a + (1 - a) = 1 by ring, Real.rpow_one]

private lemma min_le_rpow_mul_rpow {x y a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : min x y ≤ x ^ a * y ^ (1 - a) := by
  have hm : 0 ≤ min x y := le_min hx hy
  nth_rewrite 1 [← zpow_helper (min x y) a hm ha0 ha1]
  apply mul_le_mul
  · exact Real.rpow_le_rpow hm (min_le_left x y) ha0
  · exact Real.rpow_le_rpow hm (min_le_right x y) (by linarith)
  · exact Real.rpow_nonneg hm (1-a)
  · exact Real.rpow_nonneg hx a

private lemma key_expand (d n : ℕ) (hd : 1 ≤ d) (hn : 3 ≤ n) (K₁ K₂ s r q t L : ℝ)
    (hK1 : 0 < K₁) (hK2 : 0 < K₂) (hs : 0 < s) (hr : 0 < r) (hq : 0 < q)
    (ht : 0 < t) (hL : 0 < L) :
    (K₁ * s^2 * (s/t)^n * L * (5^(n+1) * r^(n+1)))^(1/(n:ℝ))
      * (K₂ * s^2 * r^2 * q^(n-1))^(((n:ℝ)-1)/(n:ℝ))
      * (2^(2*d-1)/(s^(d-1)*r^(d-1)*q))
    = K₁^(1/(n:ℝ)) * K₂^(((n:ℝ)-1)/(n:ℝ)) * 5^(((n:ℝ)+1)/(n:ℝ)) * 2^(2*(d:ℝ)-1)
        * s^(4-(d:ℝ)) * r^(4-(d:ℝ)-1/(n:ℝ)) * q^((n:ℝ)-3+1/(n:ℝ)) * t^(-(1:ℝ)) * L^(1/(n:ℝ)) := by
  have hlA : Real.log (K₁ * s^2 * (s/t)^n * L * (5^(n+1) * r^(n+1)))
      = Real.log K₁ + ((2:ℕ):ℝ)*Real.log s + (n:ℝ)*(Real.log s - Real.log t) + Real.log L
        + ((n+1:ℕ):ℝ)*Real.log 5 + ((n+1:ℕ):ℝ)*Real.log r := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
        Real.log_div (by positivity) (by positivity)]
    try ring
  have hlB : Real.log (K₂ * s^2 * r^2 * q^(n-1))
      = Real.log K₂ + ((2:ℕ):ℝ)*Real.log s + ((2:ℕ):ℝ)*Real.log r
        + ((n-1:ℕ):ℝ)*Real.log q := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    try ring
  have hlD : Real.log (2^(2*d-1)/(s^(d-1)*r^(d-1)*q))
      = ((2*d-1:ℕ):ℝ)*Real.log 2 - ((d-1:ℕ):ℝ)*Real.log s - ((d-1:ℕ):ℝ)*Real.log r
        - Real.log q := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    try ring
  have hlR : Real.log (K₁^(1/(n:ℝ)) * K₂^(((n:ℝ)-1)/(n:ℝ)) * 5^(((n:ℝ)+1)/(n:ℝ))
        * 2^(2*(d:ℝ)-1) * s^(4-(d:ℝ)) * r^(4-(d:ℝ)-1/(n:ℝ)) * q^((n:ℝ)-3+1/(n:ℝ))
        * t^(-(1:ℝ)) * L^(1/(n:ℝ)))
      = (1/(n:ℝ))*Real.log K₁ + (((n:ℝ)-1)/(n:ℝ))*Real.log K₂ + (((n:ℝ)+1)/(n:ℝ))*Real.log 5
        + (2*(d:ℝ)-1)*Real.log 2 + (4-(d:ℝ))*Real.log s + (4-(d:ℝ)-1/(n:ℝ))*Real.log r
        + ((n:ℝ)-3+1/(n:ℝ))*Real.log q + (-(1:ℝ))*Real.log t + (1/(n:ℝ))*Real.log L := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_rpow (by positivity), Real.log_rpow (by positivity), Real.log_rpow (by positivity),
        Real.log_rpow (by positivity), Real.log_rpow (by positivity), Real.log_rpow (by positivity),
        Real.log_rpow (by positivity), Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
    try ring
  have hlogL : Real.log ((K₁ * s^2 * (s/t)^n * L * (5^(n+1) * r^(n+1)))^(1/(n:ℝ))
      * (K₂ * s^2 * r^2 * q^(n-1))^(((n:ℝ)-1)/(n:ℝ))
      * (2^(2*d-1)/(s^(d-1)*r^(d-1)*q)))
      = (1/(n:ℝ))*Real.log (K₁ * s^2 * (s/t)^n * L * (5^(n+1) * r^(n+1)))
        + (((n:ℝ)-1)/(n:ℝ))*Real.log (K₂ * s^2 * r^2 * q^(n-1))
        + Real.log (2^(2*d-1)/(s^(d-1)*r^(d-1)*q)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
  have hP : 0 < (K₁ * s^2 * (s/t)^n * L * (5^(n+1) * r^(n+1)))^(1/(n:ℝ))
      * (K₂ * s^2 * r^2 * q^(n-1))^(((n:ℝ)-1)/(n:ℝ))
      * (2^(2*d-1)/(s^(d-1)*r^(d-1)*q)) := by positivity
  have hR : 0 < K₁^(1/(n:ℝ)) * K₂^(((n:ℝ)-1)/(n:ℝ)) * 5^(((n:ℝ)+1)/(n:ℝ))
        * 2^(2*(d:ℝ)-1) * s^(4-(d:ℝ)) * r^(4-(d:ℝ)-1/(n:ℝ)) * q^((n:ℝ)-3+1/(n:ℝ))
        * t^(-(1:ℝ)) * L^(1/(n:ℝ)) := by positivity
  rw [← Real.exp_log hP, ← Real.exp_log hR]
  congr 1
  rw [hlogL, hlR, hlA, hlB, hlD]
  have hcn : ((n+1:ℕ):ℝ) = (n:ℝ)+1 := by push_cast; ring
  have hcn' : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by
    rw [Nat.cast_sub (show (1:ℕ) ≤ n by omega)]; push_cast; ring
  have hcd : ((d-1:ℕ):ℝ) = (d:ℝ)-1 := by
    rw [Nat.cast_sub (show (1:ℕ) ≤ d by omega)]; push_cast; ring
  have hc2d : ((2*d-1:ℕ):ℝ) = 2*(d:ℝ)-1 := by
    rw [Nat.cast_sub (show (1:ℕ) ≤ 2*d by omega)]; push_cast; ring
  rw [hcn, hcn', hcd, hc2d]
  field_simp
  try ring

private lemma key_s (d k : ℕ) :
    ((2:ℝ)^(k+1))^(4-(d:ℝ)) = (2:ℝ)^((4-(d:ℝ))*(k:ℝ)) * (2:ℝ)^(4-(d:ℝ)) := by
  rw [← Real.rpow_natCast (2:ℝ) (k+1), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (((k+1:ℕ):ℝ) * (4-(d:ℝ))) = (4-(d:ℝ))*(k:ℝ) + (4-(d:ℝ)) by push_cast; ring]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]

private lemma key_r (d n k : ℕ) :
    ((2:ℝ)^(k+1))^(4-(d:ℝ)-1/(n:ℝ))
      = (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*(k:ℝ)) * (2:ℝ)^(4-(d:ℝ)-1/(n:ℝ)) := by
  rw [← Real.rpow_natCast (2:ℝ) (k+1), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (((k+1:ℕ):ℝ) * (4-(d:ℝ)-1/(n:ℝ)))
        = (4-(d:ℝ)-1/(n:ℝ))*(k:ℝ) + (4-(d:ℝ)-1/(n:ℝ)) by push_cast; ring]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]

private lemma key_q (n k : ℕ) :
    ((2:ℝ)^(k+1))^((n:ℝ)-3+1/(n:ℝ))
      = (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*(k:ℝ)) * (2:ℝ)^((n:ℝ)-3+1/(n:ℝ)) := by
  rw [← Real.rpow_natCast (2:ℝ) (k+1), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (((k+1:ℕ):ℝ) * ((n:ℝ)-3+1/(n:ℝ)))
        = ((n:ℝ)-3+1/(n:ℝ))*(k:ℝ) + ((n:ℝ)-3+1/(n:ℝ)) by push_cast; ring]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]

private theorem box_bound (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) (K₁ K₂ : ℝ) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t L : ℝ) (k₁ k₂ k₃ : ℕ), 1 ≤ t →
      Real.log (2 * (((2 : ℝ) ^ (k₁ + 1)) / t) + 1) ≤ L →
      min (K₁ * ((2 : ℝ) ^ (k₁ + 1)) ^ 2 * (((2 : ℝ) ^ (k₁ + 1)) / t) ^ n *
            Real.log (2 * (((2 : ℝ) ^ (k₁ + 1)) / t) + 1) *
            ((5 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (k₂ + 1)) ^ (n + 1)))
          (K₂ * ((2 : ℝ) ^ (k₁ + 1)) ^ 2 * ((2 : ℝ) ^ (k₂ + 1)) ^ 2 *
            ((2 : ℝ) ^ (k₃ + 1)) ^ (n - 1)) *
        (1 / ((2 : ℝ) ^ (k₁ * (d - 1)) * (2 : ℝ) ^ (k₂ * (d - 1)) * (2 : ℝ) ^ k₃))
      ≤ C * L ^ (1 / (n : ℝ)) / t *
          (2 : ℝ) ^ ((4 - (d : ℝ)) * k₁) *
          (2 : ℝ) ^ ((4 - (d : ℝ) - 1 / (n : ℝ)) * k₂) *
          (2 : ℝ) ^ (((n : ℝ) - 3 + 1 / (n : ℝ)) * k₃) := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨K₁ ^ (1/(n:ℝ)) * K₂ ^ (((n:ℝ)-1)/(n:ℝ)) * 5 ^ (((n:ℝ)+1)/(n:ℝ)) * 2 ^ (2*(d:ℝ)-1)
      * 2 ^ (4-(d:ℝ)) * 2 ^ (4-(d:ℝ)-1/(n:ℝ)) * 2 ^ ((n:ℝ)-3+1/(n:ℝ)), by positivity, ?_⟩
  intro t L k₁ k₂ k₃ ht hLg
  set s : ℝ := (2:ℝ)^(k₁+1) with hs
  set r : ℝ := (2:ℝ)^(k₂+1) with hr
  set q : ℝ := (2:ℝ)^(k₃+1) with hq
  have hspos : 0 < s := by rw [hs]; positivity
  have hrpos : 0 < r := by rw [hr]; positivity
  have hqpos : 0 < q := by rw [hq]; positivity
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hlogpos : 0 < Real.log (2 * (s / t) + 1) := by
    apply Real.log_pos
    have h : 0 < 2 * (s / t) := by positivity
    linarith
  have h2k1 : (2:ℝ)^k₁ = s/2 := by rw [hs, pow_succ]; ring_nf
  have h2k2 : (2:ℝ)^k₂ = r/2 := by rw [hr, pow_succ]; ring_nf
  have h2k3 : (2:ℝ)^k₃ = q/2 := by rw [hq, pow_succ]; ring_nf
  have h2d : (2:ℝ)^(d-1) * (2:ℝ)^(d-1) * 2 = (2:ℝ)^(2*d-1) := by
    rw [← pow_add, ← pow_succ, show (d-1)+(d-1)+1 = 2*d-1 by omega]
  have hDeq : (1 / ((2:ℝ)^(k₁*(d-1)) * (2:ℝ)^(k₂*(d-1)) * (2:ℝ)^k₃))
      = 2^(2*d-1)/(s^(d-1)*r^(d-1)*q) := by
    have e1 : (2:ℝ)^(k₁*(d-1)) = s^(d-1)/2^(d-1) := by
      rw [pow_mul, h2k1, div_pow]
    have e2 : (2:ℝ)^(k₂*(d-1)) = r^(d-1)/2^(d-1) := by
      rw [pow_mul, h2k2, div_pow]
    rw [e1, e2, h2k3, div_mul_div_comm, div_mul_div_comm, one_div_div, h2d]
  have hkey := key_expand d n hd1 hn K₁ K₂ s r q t (Real.log (2 * (s / t) + 1))
      hK₁ hK₂ hspos hrpos hqpos ht0 hlogpos
  have hs4 : s ^ (4-(d:ℝ)) = (2:ℝ)^((4-(d:ℝ))*k₁) * (2:ℝ)^(4-(d:ℝ)) := by
    rw [hs]; exact key_s d k₁
  have hr4 : r ^ (4-(d:ℝ)-1/(n:ℝ))
      = (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*k₂) * (2:ℝ)^(4-(d:ℝ)-1/(n:ℝ)) := by
    rw [hr]; exact key_r d n k₂
  have hq4 : q ^ ((n:ℝ)-3+1/(n:ℝ))
      = (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*k₃) * (2:ℝ)^((n:ℝ)-3+1/(n:ℝ)) := by
    rw [hq]; exact key_q n k₃
  have hlogle : Real.log (2 * (s / t) + 1) ^ (1/(n:ℝ)) ≤ L ^ (1/(n:ℝ)) :=
    Real.rpow_le_rpow (le_of_lt hlogpos) hLg (by positivity)
  have hθ0 : 0 ≤ 1/(n:ℝ) := by positivity
  have hθ1 : 1/(n:ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hexp : 1 - 1/(n:ℝ) = ((n:ℝ)-1)/(n:ℝ) := by field_simp; try ring
  have hminabs : min (K₁ * s^2 * (s/t)^n * Real.log (2*(s/t)+1) * (5^(n+1) * r^(n+1)))
        (K₂ * s^2 * r^2 * q^(n-1))
      ≤ (K₁ * s^2 * (s/t)^n * Real.log (2*(s/t)+1) * (5^(n+1) * r^(n+1)))^(1/(n:ℝ))
        * (K₂ * s^2 * r^2 * q^(n-1))^(((n:ℝ)-1)/(n:ℝ)) := by
    rw [← hexp]
    exact min_le_rpow_mul_rpow (x := K₁ * s^2 * (s/t)^n * Real.log (2*(s/t)+1) * (5^(n+1) * r^(n+1)))
      (y := K₂ * s^2 * r^2 * q^(n-1)) (a := 1/(n:ℝ)) (by positivity) (by positivity) hθ0 hθ1
  have hminD : min (K₁ * s^2 * (s/t)^n * Real.log (2*(s/t)+1) * (5^(n+1) * r^(n+1)))
        (K₂ * s^2 * r^2 * q^(n-1)) * (2^(2*d-1)/(s^(d-1)*r^(d-1)*q))
      ≤ (K₁ * s^2 * (s/t)^n * Real.log (2*(s/t)+1) * (5^(n+1) * r^(n+1)))^(1/(n:ℝ))
        * (K₂ * s^2 * r^2 * q^(n-1))^(((n:ℝ)-1)/(n:ℝ))
        * (2^(2*d-1)/(s^(d-1)*r^(d-1)*q)) :=
    mul_le_mul_of_nonneg_right hminabs (by positivity)
  rw [hDeq]
  calc min (K₁ * s^2 * (s/t)^n * Real.log (2*(s/t)+1) * (5^(n+1) * r^(n+1)))
        (K₂ * s^2 * r^2 * q^(n-1)) * (2^(2*d-1)/(s^(d-1)*r^(d-1)*q))
      ≤ (K₁ * s^2 * (s/t)^n * Real.log (2*(s/t)+1) * (5^(n+1) * r^(n+1)))^(1/(n:ℝ))
        * (K₂ * s^2 * r^2 * q^(n-1))^(((n:ℝ)-1)/(n:ℝ))
        * (2^(2*d-1)/(s^(d-1)*r^(d-1)*q)) := hminD
    _ = K₁^(1/(n:ℝ)) * K₂^(((n:ℝ)-1)/(n:ℝ)) * 5^(((n:ℝ)+1)/(n:ℝ)) * 2^(2*(d:ℝ)-1)
        * s^(4-(d:ℝ)) * r^(4-(d:ℝ)-1/(n:ℝ)) * q^((n:ℝ)-3+1/(n:ℝ)) * t^(-(1:ℝ))
        * Real.log (2*(s/t)+1)^(1/(n:ℝ)) := hkey
    _ ≤ K₁^(1/(n:ℝ)) * K₂^(((n:ℝ)-1)/(n:ℝ)) * 5^(((n:ℝ)+1)/(n:ℝ)) * 2^(2*(d:ℝ)-1)
        * s^(4-(d:ℝ)) * r^(4-(d:ℝ)-1/(n:ℝ)) * q^((n:ℝ)-3+1/(n:ℝ)) * t^(-(1:ℝ))
        * L^(1/(n:ℝ)) := mul_le_mul_of_nonneg_left hlogle (by positivity)
    _ = (K₁ ^ (1/(n:ℝ)) * K₂ ^ (((n:ℝ)-1)/(n:ℝ)) * 5 ^ (((n:ℝ)+1)/(n:ℝ)) * 2 ^ (2*(d:ℝ)-1)
        * 2 ^ (4-(d:ℝ)) * 2 ^ (4-(d:ℝ)-1/(n:ℝ)) * 2 ^ ((n:ℝ)-3+1/(n:ℝ)))
        * L^(1/(n:ℝ)) / t * (2:ℝ)^((4-(d:ℝ))*k₁) * (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*k₂)
        * (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*k₃) := by
        rw [hs4, hr4, hq4, Real.rpow_neg_one, div_eq_mul_inv]; try ring

private theorem sum_k3_le (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k₁ k₂ : ℕ,
      (∑ k₃ ∈ Finset.range (k₁ + k₂ + 3), (2 : ℝ) ^ (((n : ℝ) - 3 + 1 / (n : ℝ)) * k₃))
        ≤ C * (2 : ℝ) ^ (((n : ℝ) - 3 + 1 / (n : ℝ)) * (k₁ + k₂ + 2)) := by
  set γ : ℝ := (n:ℝ) - 3 + 1/(n:ℝ) with hγdef
  have hγpos : 0 < γ := by
    rw [hγdef]
    have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn
    have h1n : 0 < 1/(n:ℝ) := by positivity
    linarith
  refine ⟨(2:ℝ)^γ/((2:ℝ)^γ - 1), ?_, ?_⟩
  · apply div_pos
    · positivity
    · have hh : 1 < (2:ℝ)^γ := Real.one_lt_rpow (by norm_num) hγpos
      linarith
  · intro k₁ k₂
    set a : ℝ := (2:ℝ)^γ with hadef
    have ha1 : 1 < a := by rw [hadef]; exact Real.one_lt_rpow (by norm_num) hγpos
    have hane : a ≠ 1 := ne_of_gt ha1
    have hterm : ∀ k : ℕ, (2:ℝ)^(γ*k) = a^k := by
      intro k
      rw [hadef]
      show (2:ℝ)^(γ*k) = ((2:ℝ)^γ)^k
      rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) γ k]
    have h2 : (2:ℝ)^(γ*(↑k₁+↑k₂+2)) = a^(k₁+k₂+2) := by
      rw [hadef, ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) γ (k₁+k₂+2)]
      congr 1; push_cast; ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k), h2]
    rw [geom_sum_eq hane (k₁+k₂+3)]
    have hd : 0 < a - 1 := by linarith
    have hle : a^(k₁+k₂+3) - 1 ≤ a^(k₁+k₂+3) := sub_le_self _ (by norm_num)
    have h1 : (a^(k₁+k₂+3) - 1)/(a-1) ≤ a^(k₁+k₂+3)/(a-1) :=
      div_le_div_of_nonneg_right hle (le_of_lt hd)
    have h3 : a^(k₁+k₂+3)/(a-1) = (a/(a-1)) * a^(k₁+k₂+2) := by
      rw [pow_succ]; field_simp; try ring
    exact h1.trans (le_of_eq h3)

private lemma sum_range_ite (g : ℕ → ℝ) (m n' : ℕ) (h : m + 1 ≤ n') :
    (∑ k ∈ Finset.range n', (if k ≤ m then g k else 0)) = ∑ k ∈ Finset.range (m+1), g k := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private lemma two_pow_mul_le (a : ℝ) (ha : 0 ≤ a) (m K : ℕ) (hm : m ≤ K) (X : ℝ)
    (hX : (2:ℝ)^K ≤ X) : (2:ℝ)^(a * m) ≤ X ^ a := by
  have h1 : (2:ℝ)^(a*m) = ((2:ℝ)^m)^a := by
    rw [mul_comm a (m:ℝ), ← Real.rpow_natCast (2:ℝ) m,
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (m:ℝ) a]
  rw [h1]
  refine Real.rpow_le_rpow (by positivity) ?_ ha
  calc (2:ℝ)^m ≤ (2:ℝ)^K := by gcongr; norm_num
    _ ≤ X := hX

private lemma sum_two_pow_le (a : ℝ) (ha : 0 ≤ a) (K : ℕ) (X : ℝ) (hX : (2:ℝ)^K ≤ X) :
    (∑ m ∈ Finset.range (K+1), (2:ℝ)^(a*m)) ≤ ((K:ℝ)+1) * X^a := by
  calc (∑ m ∈ Finset.range (K+1), (2:ℝ)^(a*m)) ≤ ∑ m ∈ Finset.range (K+1), X^a :=
        Finset.sum_le_sum (fun m hm => two_pow_mul_le a ha m K
          (by simpa [Finset.mem_range] using hm) X hX)
    _ = ((K:ℝ)+1) * X^a := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

private lemma sum_prod_factor (f g : ℕ → ℝ) (s t : Finset ℕ) (c : ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, c * f x * g y) = c * (∑ x ∈ s, f x) * (∑ y ∈ t, g y) := by
  have h1 : ∀ x, (∑ y ∈ t, c * f x * g y) = (c * f x) * (∑ y ∈ t, g y) := by
    intro x; rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.sum_mul, ← Finset.mul_sum]
  try ring


theorem deg_pair_sum_arith (d n : ℕ) (K₁ K₂ : ℝ) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hd : 2 ≤ d) (hdn : d ≤ n) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X t : ℝ) (K : ℕ),
      2 ≤ X → 1 ≤ t → (2 : ℝ) ^ K ≤ X →
      (∑ k ∈ ((Finset.range (K + 1)).product
            ((Finset.range (K + 1)).product (Finset.range (2 * K + 3)))).filter
              (fun k => k.2.2 ≤ k.1 + k.2.1 + 2),
          min (K₁ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * (((2 : ℝ) ^ (k.1 + 1)) / t) ^ n *
                Real.log (2 * (((2 : ℝ) ^ (k.1 + 1)) / t) + 1) *
                ((5 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (k.2.1 + 1)) ^ (n + 1)))
              (K₂ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * ((2 : ℝ) ^ (k.2.1 + 1)) ^ 2 *
                ((2 : ℝ) ^ (k.2.2 + 1)) ^ (n - 1)) *
            (1 / ((2 : ℝ) ^ (k.1 * (d - 1)) * (2 : ℝ) ^ (k.2.1 * (d - 1)) *
              (2 : ℝ) ^ k.2.2)))
      ≤ C * (1 + Real.log X) ^ (1 / (n : ℝ)) *
          X ^ (2 * ((n : ℝ) + 1 - (d : ℝ)) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 2 / t := by
  obtain ⟨Cb, hCbpos, hCb⟩ := box_bound d n hd hn K₁ K₂ hK₁ hK₂
  obtain ⟨Ck, hCkpos, hCk⟩ := sum_k3_le n hn
  refine ⟨Cb * Ck * 2 ^ (2 * ((n:ℝ) - 3 + 1 / (n:ℝ))) * (2 / Real.log 2) ^ 2
      * (Real.log 5 + 1) ^ (1 / (n:ℝ)), by positivity, ?_⟩
  intro X t K hX ht h2K
  set LK : ℝ := Real.log (2 * (2:ℝ)^(K+1) + 1) with hLKdef
  set g : ℕ × (ℕ × ℕ) → ℝ := (fun k => (2:ℝ)^((4-(d:ℝ))*k.1)
      * (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*k.2.1)
      * (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*k.2.2)) with hgdef
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hX0 : (0:ℝ) < X := by linarith
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hlogX_nn : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLle : ∀ k : ℕ × (ℕ × ℕ), k ∈ ((Finset.range (K + 1)).product
        ((Finset.range (K + 1)).product (Finset.range (2 * K + 3)))).filter
          (fun k => k.2.2 ≤ k.1 + k.2.1 + 2) →
        Real.log (2 * (((2:ℝ)^(k.1+1))/t) + 1) ≤ LK := by
    intro k hk
    obtain ⟨hkprod, _⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, _⟩ := Finset.mem_product.mp hkprod
    have hk1le : k.1 ≤ K := by have := Finset.mem_range.mp hk1; omega
    rw [hLKdef]
    apply Real.log_le_log (by positivity)
    have h1 : 2 * ((2:ℝ)^(k.1+1) / t) ≤ 2 * (2:ℝ)^(K+1) := by
      have hmid : 2 * ((2:ℝ)^(k.1+1) / t) ≤ 2 * (2:ℝ)^(k.1+1) := by
        rw [← mul_div_assoc, div_le_iff₀ ht0]
        nlinarith [show (0:ℝ) ≤ 2*(2:ℝ)^(k.1+1) by positivity, ht]
      have h2 : 2 * (2:ℝ)^(k.1+1) ≤ 2 * (2:ℝ)^(K+1) := by gcongr; norm_num
      linarith
    linarith
  have hpt : ∀ k ∈ ((Finset.range (K + 1)).product
        ((Finset.range (K + 1)).product (Finset.range (2 * K + 3)))).filter
          (fun k => k.2.2 ≤ k.1 + k.2.1 + 2),
        min (K₁ * ((2:ℝ)^(k.1+1))^2 * (((2:ℝ)^(k.1+1))/t)^n
              * Real.log (2*(((2:ℝ)^(k.1+1))/t)+1)
              * ((5:ℝ)^(n+1) * ((2:ℝ)^(k.2.1+1))^(n+1)))
            (K₂ * ((2:ℝ)^(k.1+1))^2 * ((2:ℝ)^(k.2.1+1))^2 * ((2:ℝ)^(k.2.2+1))^(n-1))
          * (1 / ((2:ℝ)^(k.1*(d-1)) * (2:ℝ)^(k.2.1*(d-1)) * (2:ℝ)^k.2.2))
        ≤ Cb * LK^(1/(n:ℝ)) / t * g k := by
    intro k hk
    simpa [hgdef, mul_assoc] using hCb t LK k.1 k.2.1 k.2.2 ht (hLle k hk)
  have hlog2le : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hKle : (K:ℝ) ≤ Real.log X / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos, ← Real.log_pow (2:ℝ) K]
    exact Real.log_le_log (by positivity) h2K
  have hratio : (1:ℝ) ≤ Real.log X / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]; linarith
  have hK1 : (K:ℝ) + 1 ≤ (2/Real.log 2) * (1 + Real.log X) := by
    have h1 : (K:ℝ) + 1 ≤ 2 * (Real.log X / Real.log 2) := by linarith
    have h2 : 2 * (Real.log X / Real.log 2) = (2/Real.log 2) * Real.log X := by ring
    rw [h2] at h1
    have h3 : (2/Real.log 2) * Real.log X ≤ (2/Real.log 2) * (1 + Real.log X) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hK1sq : ((K:ℝ)+1)^2 ≤ (2/Real.log 2)^2 * (1 + Real.log X)^2 := by
    have h0 : (0:ℝ) ≤ (K:ℝ)+1 := by positivity
    have hh := pow_le_pow_left₀ h0 hK1 2
    rwa [mul_pow] at hh
  have hLKnn : 0 ≤ LK := by
    rw [hLKdef]; apply Real.log_nonneg
    have h1 : (1:ℝ) ≤ (2:ℝ)^(K+1) := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hLKle : LK ≤ (Real.log 5 + 1) * (1 + Real.log X) := by
    rw [hLKdef]
    have harg : 2 * (2:ℝ)^(K+1) + 1 ≤ 5 * X := by
      have h2K1 : (2:ℝ)^(K+1) ≤ 2 * X := by rw [pow_succ]; nlinarith [h2K]
      linarith
    calc Real.log (2 * (2:ℝ)^(K+1) + 1) ≤ Real.log (5*X) := Real.log_le_log (by positivity) harg
      _ = Real.log 5 + Real.log X := Real.log_mul (by norm_num) (ne_of_gt hX0)
      _ ≤ (Real.log 5 + 1) * (1 + Real.log X) := by
          have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
          nlinarith
  have hLKpow : LK ^ (1/(n:ℝ)) ≤ (Real.log 5 + 1)^(1/(n:ℝ)) * (1 + Real.log X)^(1/(n:ℝ)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow hLKnn hLKle (by positivity)
  have hE10 : (0:ℝ) ≤ (n:ℝ)+1-(d:ℝ)+1/(n:ℝ) := by
    have hdn' : (d:ℝ) ≤ n := by exact_mod_cast hdn
    have : 0 < 1/(n:ℝ) := by positivity
    linarith
  have hE20 : (0:ℝ) ≤ (n:ℝ)+1-(d:ℝ) := by
    have hdn' : (d:ℝ) ≤ n := by exact_mod_cast hdn
    linarith
  have hfac : ∀ k1 k2_1 : ℕ,
      (2:ℝ)^((4-(d:ℝ))*k1) * (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*k2_1)
        * (Ck * (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*(↑k1+↑k2_1+2)))
        = Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ))) * (2:ℝ)^(((n:ℝ)+1-(d:ℝ)+1/(n:ℝ))*k1)
          * (2:ℝ)^(((n:ℝ)+1-(d:ℝ))*k2_1) := by
    intro k1 k2_1
    rw [show (2:ℝ)^((4-(d:ℝ))*k1) * (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*k2_1)
          * (Ck * (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*(↑k1+↑k2_1+2)))
        = Ck * ((2:ℝ)^((4-(d:ℝ))*k1) * (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*(↑k1+↑k2_1+2))
          * (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*k2_1)) by ring]
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    rw [show (4-(d:ℝ))*k1 + ((n:ℝ)-3+1/(n:ℝ))*(↑k1+↑k2_1+2) + (4-(d:ℝ)-1/(n:ℝ))*k2_1
          = ((n:ℝ)+1-(d:ℝ)+1/(n:ℝ))*k1 + ((n:ℝ)+1-(d:ℝ))*k2_1
            + 2*((n:ℝ)-3+1/(n:ℝ)) by ring]
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    ring
  have hgbound : (∑ k ∈ ((Finset.range (K + 1)).product
        ((Finset.range (K + 1)).product (Finset.range (2 * K + 3)))).filter
          (fun k => k.2.2 ≤ k.1 + k.2.1 + 2), g k)
      ≤ Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ))) * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ)+1/(n:ℝ)))
        * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ))) := by
    have hr : (∑ k ∈ ((Finset.range (K + 1)).product
          ((Finset.range (K + 1)).product (Finset.range (2 * K + 3)))).filter
            (fun k => k.2.2 ≤ k.1 + k.2.1 + 2), g k)
        = ∑ k1 ∈ Finset.range (K+1), ∑ k2_1 ∈ Finset.range (K+1),
            ∑ k3 ∈ Finset.range (k1+k2_1+3), g (k1,(k2_1,k3)) := by
      rw [Finset.sum_filter]
      rw [show (Finset.range (K+1)).product ((Finset.range (K+1)).product (Finset.range (2*K+3)))
            = (Finset.range (K+1)) ×ˢ ((Finset.range (K+1)) ×ˢ (Finset.range (2*K+3))) from rfl]
      simp only [Finset.sum_product]
      refine Finset.sum_congr rfl (fun k1 hk1 => Finset.sum_congr rfl (fun k2_1 hk2_1 => ?_))
      have hk1le : k1 ≤ K := by have := Finset.mem_range.mp hk1; omega
      have hk2le : k2_1 ≤ K := by have := Finset.mem_range.mp hk2_1; omega
      exact sum_range_ite (fun k3 => g (k1,(k2_1,k3))) (k1+k2_1+2) (2*K+3) (by omega)
    rw [hr]
    have hinner : ∀ k1 k2_1 : ℕ,
        (∑ k3 ∈ Finset.range (k1+k2_1+3), g (k1,(k2_1,k3)))
          ≤ (2:ℝ)^((4-(d:ℝ))*k1) * (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*k2_1)
            * (Ck * (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*(↑k1+↑k2_1+2))) := by
      intro k1 k2_1
      have hgs : (∑ k3 ∈ Finset.range (k1+k2_1+3), g (k1,(k2_1,k3)))
          = (2:ℝ)^((4-(d:ℝ))*k1) * (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*k2_1)
            * (∑ k3 ∈ Finset.range (k1+k2_1+3), (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*k3)) := by
        rw [hgdef]; simp only; rw [← Finset.mul_sum]
      rw [hgs]
      exact mul_le_mul_of_nonneg_left (hCk k1 k2_1) (by positivity)
    calc (∑ k1 ∈ Finset.range (K+1), ∑ k2_1 ∈ Finset.range (K+1),
            ∑ k3 ∈ Finset.range (k1+k2_1+3), g (k1,(k2_1,k3)))
        ≤ ∑ k1 ∈ Finset.range (K+1), ∑ k2_1 ∈ Finset.range (K+1),
            (2:ℝ)^((4-(d:ℝ))*k1) * (2:ℝ)^((4-(d:ℝ)-1/(n:ℝ))*k2_1)
              * (Ck * (2:ℝ)^(((n:ℝ)-3+1/(n:ℝ))*(↑k1+↑k2_1+2))) :=
          Finset.sum_le_sum (fun k1 _ => Finset.sum_le_sum (fun k2_1 _ => hinner k1 k2_1))
      _ = Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
            * (∑ k1 ∈ Finset.range (K+1), (2:ℝ)^(((n:ℝ)+1-(d:ℝ)+1/(n:ℝ))*k1))
            * (∑ k2_1 ∈ Finset.range (K+1), (2:ℝ)^(((n:ℝ)+1-(d:ℝ))*k2_1)) := by
          rw [Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun k2_1 _ => hfac k1 k2_1))]
          rw [sum_prod_factor (fun x => (2:ℝ)^(((n:ℝ)+1-(d:ℝ)+1/(n:ℝ))*x))
                (fun y => (2:ℝ)^(((n:ℝ)+1-(d:ℝ))*y)) (Finset.range (K+1)) (Finset.range (K+1))
                (Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ))))]
      _ ≤ Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
            * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ)+1/(n:ℝ)))
            * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ))) := by
          have h1 := sum_two_pow_le ((n:ℝ)+1-(d:ℝ)+1/(n:ℝ)) hE10 K X h2K
          have h2 := sum_two_pow_le ((n:ℝ)+1-(d:ℝ)) hE20 K X h2K
          have hc : (0:ℝ) ≤ Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ))) := by positivity
          calc Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
                * (∑ k1 ∈ Finset.range (K+1), (2:ℝ)^(((n:ℝ)+1-(d:ℝ)+1/(n:ℝ))*k1))
                * (∑ k2_1 ∈ Finset.range (K+1), (2:ℝ)^(((n:ℝ)+1-(d:ℝ))*k2_1))
              ≤ Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
                * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ)+1/(n:ℝ)))
                * (∑ k2_1 ∈ Finset.range (K+1), (2:ℝ)^(((n:ℝ)+1-(d:ℝ))*k2_1)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_left h1 hc
            _ ≤ Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
                * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ)+1/(n:ℝ)))
                * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ))) := by
                apply mul_le_mul_of_nonneg_left h2
                positivity
  have hS : (∑ k ∈ ((Finset.range (K + 1)).product
        ((Finset.range (K + 1)).product (Finset.range (2 * K + 3)))).filter
          (fun k => k.2.2 ≤ k.1 + k.2.1 + 2),
        min (K₁ * ((2:ℝ)^(k.1+1))^2 * (((2:ℝ)^(k.1+1))/t)^n
              * Real.log (2*(((2:ℝ)^(k.1+1))/t)+1)
              * ((5:ℝ)^(n+1) * ((2:ℝ)^(k.2.1+1))^(n+1)))
            (K₂ * ((2:ℝ)^(k.1+1))^2 * ((2:ℝ)^(k.2.1+1))^2 * ((2:ℝ)^(k.2.2+1))^(n-1))
          * (1 / ((2:ℝ)^(k.1*(d-1)) * (2:ℝ)^(k.2.1*(d-1)) * (2:ℝ)^k.2.2)))
      ≤ Cb * LK^(1/(n:ℝ)) / t * (∑ k ∈ ((Finset.range (K + 1)).product
        ((Finset.range (K + 1)).product (Finset.range (2 * K + 3)))).filter
          (fun k => k.2.2 ≤ k.1 + k.2.1 + 2), g k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  refine hS.trans ?_
  refine (mul_le_mul_of_nonneg_left hgbound (by positivity)).trans ?_
  have hXs : Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
        * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ)+1/(n:ℝ))) * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ)))
      = Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
        * (((K:ℝ)+1)^2 * X^(2*((n:ℝ)+1-(d:ℝ))+1/(n:ℝ))) := by
    rw [show Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ))) * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ)+1/(n:ℝ)))
          * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ)))
        = Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
          * (((K:ℝ)+1)^2 * (X^((n:ℝ)+1-(d:ℝ)+1/(n:ℝ)) * X^((n:ℝ)+1-(d:ℝ)))) by ring]
    rw [← Real.rpow_add hX0,
        show ((n:ℝ)+1-(d:ℝ)+1/(n:ℝ)) + ((n:ℝ)+1-(d:ℝ)) = 2*((n:ℝ)+1-(d:ℝ))+1/(n:ℝ) by ring]
  have hfinal :
      Cb * LK^(1/(n:ℝ)) / t * (Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
        * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ)+1/(n:ℝ))) * (((K:ℝ)+1) * X^((n:ℝ)+1-(d:ℝ))))
      ≤ (Cb * Ck * 2 ^ (2 * ((n:ℝ)-3 + 1 / (n:ℝ))) * (2 / Real.log 2) ^ 2
          * (Real.log 5 + 1) ^ (1 / (n:ℝ))) * (1 + Real.log X)^(1/(n:ℝ))
        * X ^ (2 * ((n:ℝ) + 1 - (d:ℝ)) + 1 / (n:ℝ)) * (1 + Real.log X)^2 / t := by
    rw [hXs]
    rw [show Cb * LK^(1/(n:ℝ)) / t * (Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ)))
          * (((K:ℝ)+1)^2 * X^(2*((n:ℝ)+1-(d:ℝ))+1/(n:ℝ))))
        = (Cb * Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ))) * X^(2*((n:ℝ)+1-(d:ℝ))+1/(n:ℝ)) / t)
          * (LK^(1/(n:ℝ)) * ((K:ℝ)+1)^2) by ring_nf]
    rw [show (Cb * Ck * 2 ^ (2 * ((n:ℝ)-3 + 1 / (n:ℝ))) * (2 / Real.log 2) ^ 2
          * (Real.log 5 + 1) ^ (1 / (n:ℝ))) * (1 + Real.log X)^(1/(n:ℝ))
        * X ^ (2 * ((n:ℝ) + 1 - (d:ℝ)) + 1 / (n:ℝ)) * (1 + Real.log X)^2 / t
        = (Cb * Ck * (2:ℝ)^(2*((n:ℝ)-3+1/(n:ℝ))) * X^(2*((n:ℝ)+1-(d:ℝ))+1/(n:ℝ)) / t)
          * ((Real.log 5 + 1)^(1/(n:ℝ)) * (1 + Real.log X)^(1/(n:ℝ))
              * ((2 / Real.log 2)^2 * (1 + Real.log X)^2)) by ring_nf]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hLKpow hK1sq (by positivity) (by positivity)
  exact hfinal

end Work.HP.MM2
