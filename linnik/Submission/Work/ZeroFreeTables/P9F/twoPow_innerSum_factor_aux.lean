/-
# The two-digit (`p = 2`) peel for the cubic character correlation, in the `gaussSum` bubble

The workspace has two `Commons` clusters that cannot be imported together:
`...DirichletCharacter.charCorrelation_twoPow` and `...DirichletCharacter.gaussSum_normSq_eq_conductor`
both declare `Common.NumberTheory.DirichletCharacter.sum_zmod_eq_sum_range`.  The `p = 2` counting
lemmas of `lfSmall/` live in the second cluster, while the existing 2-adic peel
(`Submission/Work/LinnikBurgess/thetaTwo_core.lean`, `twoPow_innerSum_factor.lean`) lives in the
first, so it cannot be imported by a file that also needs the counting.  This file re-proves the peel
in the second cluster: the truncated exponential `thetaTwo` arithmetic (transcribed from
`thetaTwo_core.lean`) and the factorisation `twoPow_innerSum_factor` (transcribed from
`twoPow_innerSum_factor.lean`), with the single `charCorrelation_twoPow` ingredient
`chi_one_add_twoPow_sub_one` taken from `Work/ZeroFreeTables/P9F/twoPow_api.lean`.

`thetaTwo e m u = 1 + 2^m u + 2^(2m-1) u^2` in `ZMod (2^e)` behaves like `u ↦ 1 + 2^m u` when
`3m ≥ e+1`: it is multiplicative, every value is a unit, `1 + 2^m t = thetaTwo e m (t - 2^(m-1)t^2)`,
and `thetaTwo e m 1` generates a cyclic subgroup on which a primitive character is faithful, so
`χ (thetaTwo e m 1)` is a primitive `2^(e-m)`-th root of unity.
-/
import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.corr6_twoPow_defs
import Submission.Work.ZeroFreeTables.P9F.twoPow_api

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.ZeroFreeTables.P9F.TwoPowAux

open scoped BigOperators
open Work.LinnikBurgess


open scoped BigOperators

/-- In `ZMod (2^e)` the class of `2^k` vanishes as soon as `e ≤ k`. -/
lemma twoPow_cast_eq_zero {e k : ℕ} (hk : e ≤ k) : ((2 ^ k : ℕ) : ZMod (2 ^ e)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow 2 hk

/-- Same, for the `2`-power taken inside the ring. -/
lemma twoPow_pow_eq_zero {e k : ℕ} (hk : e ≤ k) : (2 : ZMod (2 ^ e)) ^ k = 0 := by
  have := twoPow_cast_eq_zero (e := e) hk
  simpa using this

lemma mul_pow_pow {e : ℕ} (x : ZMod (2 ^ e)) (i j : ℕ) : x ^ i * x ^ j = x ^ (i + j) :=
  (pow_add x i j).symm

lemma two_mul_pow_eq {e k : ℕ} :
    (2 : ZMod (2 ^ e)) * (2 : ZMod (2 ^ e)) ^ k = (2 : ZMod (2 ^ e)) ^ (k + 1) :=
  (pow_succ' _ _).symm

lemma thetaTwo_zero (e m : ℕ) : thetaTwo e m (0 : ZMod (2 ^ e)) = 1 := by
  simp [thetaTwo]

/-- `thetaTwo` is additive-to-multiplicative, provided the correction terms are killed by `2^e`. -/
lemma thetaTwo_add {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (u v : ZMod (2 ^ e)) :
    thetaTwo e m (u + v) = thetaTwo e m u * thetaTwo e m v := by
  have h3m : e ≤ 3 * m - 1 := by omega
  have h4m : e ≤ 4 * m - 2 := by omega
  have hm2 : 2 ≤ m := by omega
  set A : ZMod (2 ^ e) := (2 : ZMod (2 ^ e)) ^ m with hA
  set B : ZMod (2 ^ e) := (2 : ZMod (2 ^ e)) ^ (m - 1) with hB
  set C : ZMod (2 ^ e) := A * B with hC
  have hθ : ∀ x : ZMod (2 ^ e), thetaTwo e m x = 1 + A * x + C * x ^ 2 := by
    intro x
    rw [thetaTwo]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [show (2 : ZMod (2 ^ e)) ^ (2 * m - 1) = A * B by
      rw [hA, hB, ← pow_add]
      congr 1
      omega]
  have hA2 : A ^ 2 = 2 * C := by
    have e1 : A ^ 2 = (2 : ZMod (2 ^ e)) ^ (m + m) := by
      rw [hA, pow_two]; rw [mul_pow_pow]
    have e2 : 2 * C = (2 : ZMod (2 ^ e)) ^ (m + (m - 1) + 1) := by
      rw [hC, hA, hB]; rw [mul_pow_pow]; rw [two_mul_pow_eq]
    rw [e1, e2, show m + m = m + (m - 1) + 1 by omega]
  have hAC : A * C = 0 := by
    rw [hC, hA, hB]; rw [mul_pow_pow]; rw [mul_pow_pow]
    rw [show m + (m + (m - 1)) = 3 * m - 1 by omega]
    exact twoPow_pow_eq_zero h3m
  have hC2 : C ^ 2 = 0 := by
    rw [hC, hA, hB]; rw [mul_pow_pow]; rw [← pow_mul]
    rw [show (m + (m - 1)) * 2 = 4 * m - 2 by omega]
    exact twoPow_pow_eq_zero h4m
  calc thetaTwo e m (u + v)
      = 1 + A * (u + v) + C * (u + v) ^ 2 := hθ (u + v)
    _ = 1 + A * (u + v) + C * (u + v) ^ 2
          + ((A ^ 2 - 2 * C) * (u * v) + (A * C) * (u ^ 2 * v + u * v ^ 2)
              + (C ^ 2) * ((u ^ 2) * (v ^ 2))) := by
        rw [show A ^ 2 - 2 * C = 0 by rw [hA2]; ring, hAC, hC2]; ring
    _ = thetaTwo e m u * thetaTwo e m v := by rw [hθ u, hθ v]; ring

/-- Every value of `thetaTwo` is a unit (`θ(u) * θ(-u) = θ(0) = 1`). -/
lemma thetaTwo_isUnit {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (u : ZMod (2 ^ e)) : IsUnit (thetaTwo e m u) := by
  have h1 : thetaTwo e m u * thetaTwo e m (-u) = 1 := by
    rw [← thetaTwo_add hm he h3, add_neg_cancel, thetaTwo_zero]
  have h2 : thetaTwo e m (-u) * thetaTwo e m u = 1 := by
    rw [← thetaTwo_add hm he h3, neg_add_cancel, thetaTwo_zero]
  exact ⟨⟨thetaTwo e m u, thetaTwo e m (-u), h1, h2⟩, rfl⟩

/-- The "two-digit" identity: `1 + 2^m t = thetaTwo e m (t - 2^(m-1) t^2)`. -/
lemma thetaTwo_twoDigit {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (t : ZMod (2 ^ e)) :
    1 + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * t
      = thetaTwo e m (t - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * t ^ 2) := by
  have h3m : e ≤ 3 * m - 1 := by omega
  have h4m3 : e ≤ 4 * m - 3 := by omega
  set A : ZMod (2 ^ e) := (2 : ZMod (2 ^ e)) ^ m with hA
  set B : ZMod (2 ^ e) := (2 : ZMod (2 ^ e)) ^ (m - 1) with hB
  set C : ZMod (2 ^ e) := A * B with hC
  have hθ : ∀ x : ZMod (2 ^ e), thetaTwo e m x = 1 + A * x + C * x ^ 2 := by
    intro x
    rw [thetaTwo]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [show (2 : ZMod (2 ^ e)) ^ (2 * m - 1) = A * B by
      rw [hA, hB, ← pow_add]
      congr 1
      omega]
  have hAc : ((2 ^ m : ℕ) : ZMod (2 ^ e)) = A := by rw [hA, Nat.cast_pow]; norm_num
  have hBc : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) = B := by rw [hB, Nat.cast_pow]; norm_num
  have hAB2 : 2 * A * B ^ 2 = 0 := by
    rw [hA, hB]; rw [← pow_mul]; rw [two_mul_pow_eq]; rw [mul_pow_pow]
    rw [show m + 1 + (m - 1) * 2 = 3 * m - 1 by omega]
    exact twoPow_pow_eq_zero h3m
  have hAB3 : A * B ^ 3 = 0 := by
    rw [hA, hB]; rw [← pow_mul]; rw [mul_pow_pow]
    rw [show m + (m - 1) * 3 = 4 * m - 3 by omega]
    exact twoPow_pow_eq_zero h4m3
  calc 1 + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * t
      = 1 + A * t := by rw [hAc]
    _ = 1 + A * t - 2 * A * B ^ 2 * t ^ 3 + A * B ^ 3 * t ^ 4 := by
          rw [hAB2, hAB3]; ring
    _ = 1 + A * (t - B * t ^ 2) + C * (t - B * t ^ 2) ^ 2 := by rw [hC]; ring
    _ = thetaTwo e m (t - B * t ^ 2) := (hθ (t - B * t ^ 2)).symm
    _ = thetaTwo e m (t - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * t ^ 2) := by rw [hBc]

/-- The value of `thetaTwo` at a power of two. -/
lemma thetaTwo_pow_two {e m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    thetaTwo e m ((2 : ZMod (2 ^ e)) ^ k)
      = 1 + (2 : ZMod (2 ^ e)) ^ (m + k) + (2 : ZMod (2 ^ e)) ^ (2 * m - 1 + 2 * k) := by
  set A : ZMod (2 ^ e) := (2 : ZMod (2 ^ e)) ^ m with hA
  set B : ZMod (2 ^ e) := (2 : ZMod (2 ^ e)) ^ (m - 1) with hB
  set C : ZMod (2 ^ e) := A * B with hC
  have hθ : ∀ x : ZMod (2 ^ e), thetaTwo e m x = 1 + A * x + C * x ^ 2 := by
    intro x
    rw [thetaTwo]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [show (2 : ZMod (2 ^ e)) ^ (2 * m - 1) = A * B by
      rw [hA, hB, ← pow_add]
      congr 1
      omega]
  have h1 : A * (2 : ZMod (2 ^ e)) ^ k = (2 : ZMod (2 ^ e)) ^ (m + k) := by
    rw [hA]; rw [mul_pow_pow]
  have h2 : C * ((2 : ZMod (2 ^ e)) ^ k) ^ 2 = (2 : ZMod (2 ^ e)) ^ (2 * m - 1 + 2 * k) := by
    rw [hC, hA, hB]; rw [← pow_mul]; rw [mul_pow_pow]; rw [mul_pow_pow]
    rw [show m + (m - 1) + k * 2 = 2 * m - 1 + 2 * k by omega]
  rw [hθ, h1, h2]

/-- Powers of `thetaTwo`: `θ(u)^n = θ (n u)`. -/
lemma thetaTwo_pow {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (u : ZMod (2 ^ e)) (n : ℕ) :
    thetaTwo e m u ^ n = thetaTwo e m ((n : ZMod (2 ^ e)) * u) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, thetaTwo_zero]
  | succ n ih =>
      rw [pow_succ, ih, ← thetaTwo_add hm he h3]
      congr 1
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- `θ(1)` has order dividing `2^(e-m)`. -/
lemma thetaTwo_one_pow_card {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (h2 : 2 * m ≤ e) : thetaTwo e m 1 ^ (2 ^ (e - m)) = (1 : ZMod (2 ^ e)) := by
  rw [thetaTwo_pow hm he h3 1 (2 ^ (e - m)), mul_one]
  have hc : ((2 ^ (e - m) : ℕ) : ZMod (2 ^ e)) = (2 : ZMod (2 ^ e)) ^ (e - m) := by
    rw [Nat.cast_pow]; norm_num
  rw [hc, thetaTwo_pow_two hm (e - m)]
  rw [show m + (e - m) = e by omega, show 2 * m - 1 + 2 * (e - m) = 2 * e - 1 by omega]
  rw [twoPow_pow_eq_zero (le_refl e), twoPow_pow_eq_zero (by omega : e ≤ 2 * e - 1)]
  ring

/-- The exact half-power value: `θ(1)^(2^(e-m-1)) = 1 + 2^(e-1)`. -/
lemma thetaTwo_one_pow_half {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (h2 : 2 * m ≤ e) :
    thetaTwo e m 1 ^ (2 ^ (e - m - 1)) = ((1 + 2 ^ (e - 1) : ℕ) : ZMod (2 ^ e)) := by
  rw [thetaTwo_pow hm he h3 1 (2 ^ (e - m - 1)), mul_one]
  have hc : ((2 ^ (e - m - 1) : ℕ) : ZMod (2 ^ e)) = (2 : ZMod (2 ^ e)) ^ (e - m - 1) := by
    rw [Nat.cast_pow]; norm_num
  rw [hc, thetaTwo_pow_two hm (e - m - 1)]
  rw [show m + (e - m - 1) = e - 1 by omega,
      show 2 * m - 1 + 2 * (e - m - 1) = 2 * e - 3 by omega]
  rw [twoPow_pow_eq_zero (by omega : e ≤ 2 * e - 3)]
  push_cast
  ring

/-- `thetaTwo e m` is periodic with period `2^(e-m)`. -/
lemma thetaTwo_period {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (h2 : 2 * m ≤ e) (u n : ZMod (2 ^ e)) :
    thetaTwo e m (u + ((2 ^ (e - m) : ℕ) : ZMod (2 ^ e)) * n) = thetaTwo e m u := by
  haveI : NeZero (2 ^ e) := ⟨pow_ne_zero e (by norm_num)⟩
  have hcn : thetaTwo e m (((2 ^ (e - m) : ℕ) : ZMod (2 ^ e)) * n) = 1 := by
    have hp := thetaTwo_pow hm he h3 n (2 ^ (e - m))
    have hc : ((2 ^ (e - m) : ℕ) : ZMod (2 ^ e)) = (2 : ZMod (2 ^ e)) ^ (e - m) := by
      rw [Nat.cast_pow]; norm_num
    rw [hc] at hp ⊢
    rw [← hp]
    have h1 : thetaTwo e m n = thetaTwo e m 1 ^ n.val := by
      have hp2 := thetaTwo_pow hm he h3 1 n.val
      rw [ZMod.natCast_zmod_val, mul_one] at hp2
      exact hp2.symm
    rw [h1, ← pow_mul, Nat.mul_comm n.val (2 ^ (e - m)), pow_mul,
        thetaTwo_one_pow_card hm he h3 h2, one_pow]
  rw [thetaTwo_add hm he h3, hcn, mul_one]

/-- `χ (thetaTwo e m 1)` is a primitive `2^(e-m)`-th root of unity for primitive `χ` mod `2^e`. -/
lemma chi_thetaTwo_one_isPrimitiveRoot {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e)
    (h3 : e + 1 ≤ 3 * m) (h2 : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (2 ^ e)) (hχ : χ.IsPrimitive) :
    IsPrimitiveRoot (χ (thetaTwo e m 1)) (2 ^ (e - m)) := by
  have hpow : (χ (thetaTwo e m 1)) ^ (2 ^ (e - m)) = 1 := by
    rw [← map_pow, thetaTwo_one_pow_card hm he h3 h2, map_one]
  have hhalf : (χ (thetaTwo e m 1)) ^ (2 ^ (e - m - 1)) = -1 := by
    rw [← map_pow, thetaTwo_one_pow_half hm he h3 h2]
    exact Work.ZeroFreeTables.P9F.chi_one_add_twoPow_sub_one (by omega : 2 ≤ e) χ hχ
  rw [IsPrimitiveRoot.iff_orderOf]
  have hdvd : orderOf (χ (thetaTwo e m 1)) ∣ 2 ^ (e - m) :=
    orderOf_dvd_iff_pow_eq_one.mpr hpow
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk1 : e - m - 1 < k := by
    by_contra hcon
    push Not at hcon
    have hdvd2 : orderOf (χ (thetaTwo e m 1)) ∣ 2 ^ (e - m - 1) := by
      rw [hkeq]; exact Nat.pow_dvd_pow 2 hcon
    rw [orderOf_dvd_iff_pow_eq_one] at hdvd2
    rw [hhalf] at hdvd2
    norm_num at hdvd2
  rw [hkeq, show k = e - m by omega]




set_option maxHeartbeats 1000000

lemma mul_inv_eq_one_of_isUnit {n : ℕ} {x : ZMod n} (h : IsUnit x) : x * x⁻¹ = 1 := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, ZMod.inv_coe_unit u, ← Units.val_mul, mul_inv_cancel, Units.val_one]

lemma prod_add_twoPow_factor {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (f : Fin 3 → ZMod (2 ^ e)) (hf : ∀ l : Fin 3, IsUnit (f l)) (W : ZMod (2 ^ e)) :
    ∏ l : Fin 3, (f l + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * W)
      = (∏ l : Fin 3, f l)
        * thetaTwo e m (W * (∑ l : Fin 3, (f l)⁻¹)
            - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * W ^ 2
                * (∑ l : Fin 3, ((f l)⁻¹) ^ 2)) := by
  have hfac : ∀ l : Fin 3, f l + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * W
      = f l * thetaTwo e m (W * (f l)⁻¹
          - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * (W * (f l)⁻¹) ^ 2) := by
    intro l
    have hx : f l * (f l)⁻¹ = 1 := mul_inv_eq_one_of_isUnit (hf l)
    have hx' : (f l)⁻¹ * f l = 1 := by rw [mul_comm]; exact hx
    have h2 := thetaTwo_twoDigit hm he h3 (W * (f l)⁻¹)
    calc f l + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * W
        = f l + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * (W * ((f l)⁻¹ * f l)) := by rw [hx']; ring
      _ = f l * (1 + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * (W * (f l)⁻¹)) := by ring
      _ = f l * thetaTwo e m (W * (f l)⁻¹
              - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * (W * (f l)⁻¹) ^ 2) := by rw [h2]
  have hprod : ∏ l : Fin 3, thetaTwo e m (W * (f l)⁻¹
        - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * (W * (f l)⁻¹) ^ 2)
      = thetaTwo e m (∑ l : Fin 3, (W * (f l)⁻¹
          - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * (W * (f l)⁻¹) ^ 2)) := by
    rw [Fin.prod_univ_three, Fin.sum_univ_three]
    rw [← thetaTwo_add hm he h3]
    rw [← thetaTwo_add hm he h3]
  have hsum : ∑ l : Fin 3, (W * (f l)⁻¹
        - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * (W * (f l)⁻¹) ^ 2)
      = W * (∑ l : Fin 3, (f l)⁻¹)
          - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * W ^ 2
              * (∑ l : Fin 3, ((f l)⁻¹) ^ 2) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.mul_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
  calc ∏ l : Fin 3, (f l + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * W)
      = ∏ l : Fin 3, (f l * thetaTwo e m (W * (f l)⁻¹
          - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * (W * (f l)⁻¹) ^ 2)) := by
        apply Finset.prod_congr rfl
        intro l _
        exact hfac l
    _ = (∏ l : Fin 3, f l) * (∏ l : Fin 3, thetaTwo e m (W * (f l)⁻¹
          - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * (W * (f l)⁻¹) ^ 2)) :=
        Finset.prod_mul_distrib
    _ = (∏ l : Fin 3, f l) * thetaTwo e m (∑ l : Fin 3, (W * (f l)⁻¹
          - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * (W * (f l)⁻¹) ^ 2)) := by rw [hprod]
    _ = (∏ l : Fin 3, f l) * thetaTwo e m (W * (∑ l : Fin 3, (f l)⁻¹)
          - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * W ^ 2
              * (∑ l : Fin 3, ((f l)⁻¹) ^ 2)) := by rw [hsum]

lemma castHom_val' {e m : ℕ} (h : 2 ^ (e - m) ∣ 2 ^ e) (X : ZMod (2 ^ e)) :
    (ZMod.castHom h (ZMod (2 ^ (e - m)))) X = ((X.val : ℕ) : ZMod (2 ^ (e - m))) := by
  have hnz : NeZero (2 ^ e) := ⟨pow_ne_zero e (by norm_num)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

lemma castHom_two_sub {e m : ℕ} (h2 : 2 * m ≤ e) (hm : 1 ≤ m) :
    (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m))))
      (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e))) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m))) := by
  have hnz : NeZero (2 ^ e) := ⟨pow_ne_zero e (by norm_num)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega : m - 1 < e))]

lemma castHom_lift_val {e m : ℕ} (w : ZMod (2 ^ (e - m))) :
    (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m))))
      (((w.val : ℕ) : ZMod (2 ^ e))) = w := by
  have hnz : NeZero (2 ^ e) := ⟨pow_ne_zero e (by norm_num)⟩
  have hnz2 : NeZero (2 ^ (e - m)) := ⟨pow_ne_zero (e - m) (by norm_num)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt (by
    have h1 := ZMod.val_lt w
    have h2 : 2 ^ (e - m) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)]
  exact ZMod.natCast_zmod_val w

theorem thetaTwo_of_castHom_eq {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (h2 : 2 * m ≤ e) (X : ZMod (2 ^ e)) (z : ZMod (2 ^ (e - m)))
    (hz : (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) X = z) :
    thetaTwo e m X = thetaTwo e m 1 ^ z.val := by
  have hnz : NeZero (2 ^ e) := ⟨pow_ne_zero e (by norm_num)⟩
  have hzv : z.val = X.val % 2 ^ (e - m) := by
    rw [← hz, castHom_val' _, ZMod.val_natCast]
  have hX : X = (((X.val % 2 ^ (e - m) : ℕ)) : ZMod (2 ^ e))
      + ((2 ^ (e - m) : ℕ) : ZMod (2 ^ e)) * (((X.val / 2 ^ (e - m) : ℕ)) : ZMod (2 ^ e)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val X, ← Nat.mod_add_div X.val (2 ^ (e - m))]
    push_cast
    ring
  rw [hX, ← hzv, thetaTwo_period hm he h3 h2]
  have hp := thetaTwo_pow hm he h3 1 z.val
  rw [mul_one] at hp
  exact hp.symm

lemma conj_chi_unit {e : ℕ} (χ : DirichletCharacter ℂ (2 ^ e)) (u : ZMod (2 ^ e))
    (hu : IsUnit u) : (starRingEnd ℂ) (χ u) = χ u⁻¹ := by
  obtain ⟨v, rfl⟩ := hu
  have hmul : χ (↑v) * (starRingEnd ℂ) (χ (↑v)) = 1 := by
    rw [show (starRingEnd ℂ) (χ (↑v)) = star (χ (↑v)) from rfl, MulChar.star_apply',
      ← MulChar.mul_apply,
      show χ * χ⁻¹ = 1 by rw [mul_comm, MulChar.inv_mul]]
    exact MulChar.one_apply_coe v
  have h2 : χ (↑v) * χ (↑(v⁻¹)) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  rw [eq_inv_of_mul_eq_one_right hmul, ZMod.inv_coe_unit]
  exact (eq_inv_of_mul_eq_one_right h2).symm

/-- **The two-digit peel for the cubic correlation at `p = 2`.**  Let `e ≥ 3`, `m ≥ 1` with
`e+1 ≤ 3m` and `2m ≤ e`, `χ` primitive mod `2^e`, all six shifts `y + a_l`, `y + b_l` odd, and
`x = y + 2^m·w`.  Then the summand of the correlation factors as a constant `C(y)` (independent of
`w`) times a *quadratic* character value:
`χ (∏_l (x+a_l)) · conj (χ (∏_l (x+b_l))) = C(y) · θ₀ ^ ((α' w - 2^(m-1) γ' w²).val)`,
where `θ₀ = χ (thetaTwo e m 1)`, `α' = defect1 2 e a b y` and `γ' = defect2 2 e a b y` viewed in
`ZMod (2^(e-m))`.  Moreover `θ₀` is a primitive `2^(e-m)`-th root of unity (this is where
primitivity of `χ` enters: `thetaTwo e m 1` raised to `2^(e-m-1)` is `1 + 2^(e-1)` modulo `2^e`).

Import `Submission.Work.LinnikBurgess.corr6_twoPow_defs` (`thetaTwo`),
`Submission.Work.LinnikBurgess.burgess_lead_defs` (`UnitAt`, `defect1`, `defect2`) and
`Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation_twoPow` (which has
`chi_one_add_twoPow_sub_one : 2 ≤ e → χ.IsPrimitive → χ (1 + 2^(e-1)) = -1`).

Proof plan: write `x + a_l = (y + a_l) + 2^m w = (y+a_l)(1 + 2^m w (y+a_l)^{-1})` (the shifts are
odd, hence units), use the two-digit identity `1 + 2^m u = thetaTwo e m (u - 2^(m-1)u²)` and
multiplicativity of `thetaTwo` (both valid under `e+1 ≤ 3m`, `e ≥ 3`) to get
`∏_l (x+a_l) = (∏_l (y+a_l)) · thetaTwo e m (w·S1a - 2^(m-1)w²·S2a)`, where `S1a = ∑_l (y+a_l)^{-1}`
and `S2a = ∑_l (y+a_l)^{-2}`; similarly on the `b` side, then use multiplicativity of `χ` and
`conj (χ z) = χ z⁻¹ = χ (thetaTwo e m (-u))` for the unit `thetaTwo e m u`, so that the two phases
combine into `thetaTwo e m (w·α - 2^(m-1)w²·γ)` with `α`, `γ` the differences `S1a - S1b`,
`S2a - S2b` (these are `defect1 2 e a b y`, `defect2 2 e a b y`).  Finally rewrite
`thetaTwo e m (cast z) = (thetaTwo e m 1)^(z.val)` for `z : ZMod (2^(e-m))` (from multiplicativity,
by induction on `z.val`), and prove primitivity of `χ (thetaTwo e m 1)` by
`IsPrimitiveRoot.iff_orderOf` from `(1+2^m)^(2^(e-m)) ≡ 1` and
`(1+2^m)^(2^(e-m-1)) ≡ 1 + 2^(e-1) (mod 2^e)`, the latter because `thetaTwo e m (2^(e-m-1))` is
`1 + 2^(e-1) + 2^(2e-3) ≡ 1 + 2^(e-1)`, using `chi_one_add_twoPow_sub_one`. -/
theorem twoPow_innerSum_factor_aux {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m) (h2 : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (2 ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (y : ℕ)
    (hy : UnitAt 2 y a b) :
    IsPrimitiveRoot (χ (thetaTwo e m 1)) (2 ^ (e - m)) ∧
      (∑ w : ZMod (2 ^ (e - m)),
        χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (b l : ℕ)))))
      = (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (b l : ℕ)))))
        * (∑ w : ZMod (2 ^ (e - m)),
            (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
              - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
                * ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2)).val)) := by
  refine ⟨chi_thetaTwo_one_isPrimitiveRoot hm he h3 h2 χ hχ, ?_⟩
  set F : Fin 3 → ZMod (2 ^ e) := fun l => (((y + a l : ℕ)) : ZMod (2 ^ e)) with hF
  set G : Fin 3 → ZMod (2 ^ e) := fun l => (((y + b l : ℕ)) : ZMod (2 ^ e)) with hG
  have hFa : ∀ l : Fin 3, IsUnit (F l) := by
    intro l
    rw [hF]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by omega : 0 < e)).mpr (hy l).1
  have hGb : ∀ l : Fin 3, IsUnit (G l) := by
    intro l
    rw [hG]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by omega : 0 < e)).mpr (hy l).2
  have hcastA : ∀ l : Fin 3, (y : ZMod (2 ^ e)) + ((a l : ℕ) : ZMod (2 ^ e)) = F l := by
    intro l
    simp only [hF, Nat.cast_add]
  have hcastB : ∀ l : Fin 3, (y : ZMod (2 ^ e)) + ((b l : ℕ) : ZMod (2 ^ e)) = G l := by
    intro l
    simp only [hG, Nat.cast_add]
  have hconstA : (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((a l : ℕ) : ZMod (2 ^ e))))
      = ∏ l : Fin 3, F l := by
    apply Finset.prod_congr rfl
    intro l _
    exact hcastA l
  have hconstB : (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((b l : ℕ) : ZMod (2 ^ e))))
      = ∏ l : Fin 3, G l := by
    apply Finset.prod_congr rfl
    intro l _
    exact hcastB l
  have hpt : ∀ w : ZMod (2 ^ (e - m)),
      χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((a l : ℕ) : ZMod (2 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((b l : ℕ) : ZMod (2 ^ e)))))
      = (χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((a l : ℕ) : ZMod (2 ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((b l : ℕ) : ZMod (2 ^ e))))))
        * (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
            - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
              * ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2)).val) := by
    intro w
    set D1 : ZMod (2 ^ e) := defect1 2 e a b y with hD1
    set D2 : ZMod (2 ^ e) := defect2 2 e a b y with hD2
    set Z : ZMod (2 ^ (e - m)) :=
      (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) D1 * w
        - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
          * ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) D2 * w ^ 2) with hZ
    have hD1eq : D1 = (∑ l : Fin 3, (F l)⁻¹) - ∑ l : Fin 3, (G l)⁻¹ := rfl
    have hD2eq : D2 = (∑ l : Fin 3, ((F l)⁻¹) ^ 2) - ∑ l : Fin 3, ((G l)⁻¹) ^ 2 := rfl
    set σa : ZMod (2 ^ e) := ((w.val : ℕ) : ZMod (2 ^ e)) * (∑ l : Fin 3, (F l)⁻¹)
        - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) ^ 2
            * (∑ l : Fin 3, ((F l)⁻¹) ^ 2) with hσa
    set σb : ZMod (2 ^ e) := ((w.val : ℕ) : ZMod (2 ^ e)) * (∑ l : Fin 3, (G l)⁻¹)
        - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) ^ 2
            * (∑ l : Fin 3, ((G l)⁻¹) ^ 2) with hσb
    have hpa : ∏ l : Fin 3, (F l + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)))
        = (∏ l : Fin 3, F l) * thetaTwo e m σa := by
      rw [hσa]
      exact prod_add_twoPow_factor hm he h3 F hFa _
    have hpb : ∏ l : Fin 3, (G l + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)))
        = (∏ l : Fin 3, G l) * thetaTwo e m σb := by
      rw [hσb]
      exact prod_add_twoPow_factor hm he h3 G hGb _
    have hpA : (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((a l : ℕ) : ZMod (2 ^ e))))
        = ∏ l : Fin 3, (F l + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e))) := by
      apply Finset.prod_congr rfl
      intro l _
      rw [(hcastA l).symm]
      ring
    have hpB : (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((b l : ℕ) : ZMod (2 ^ e))))
        = ∏ l : Fin 3, (G l + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e))) := by
      apply Finset.prod_congr rfl
      intro l _
      rw [(hcastB l).symm]
      ring
    have hχA : χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((a l : ℕ) : ZMod (2 ^ e))))
        = χ (∏ l : Fin 3, F l) * χ (thetaTwo e m σa) := by
      rw [hpA, hpa, map_mul]
    have hconj : (starRingEnd ℂ) (χ (thetaTwo e m σb)) = χ (thetaTwo e m (-σb)) := by
      rw [conj_chi_unit χ _ (thetaTwo_isUnit hm he h3 σb)]
      congr 1
      exact ZMod.inv_eq_of_mul_eq_one _ _ _ (by
        rw [← thetaTwo_add hm he h3, add_neg_cancel, thetaTwo_zero])
    have hχB : (starRingEnd ℂ) (χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((b l : ℕ) : ZMod (2 ^ e)))))
        = (starRingEnd ℂ) (χ (∏ l : Fin 3, G l)) * χ (thetaTwo e m (-σb)) := by
      rw [hpB, hpb, map_mul, map_mul, hconj]
    have hsub : σa + -σb = ((w.val : ℕ) : ZMod (2 ^ e)) * D1
        - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) ^ 2 * D2 := by
      rw [hσa, hσb, hD1eq, hD2eq]
      ring
    have hzcast : (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (σa + -σb) = Z := by
      rw [hsub, hZ]
      simp only [map_sub, map_mul, map_pow]
      rw [castHom_lift_val w, castHom_two_sub h2 hm]
      ring
    calc χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((a l : ℕ) : ZMod (2 ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((b l : ℕ) : ZMod (2 ^ e)))))
        = (χ (∏ l : Fin 3, F l) * χ (thetaTwo e m σa))
            * ((starRingEnd ℂ) (χ (∏ l : Fin 3, G l)) * χ (thetaTwo e m (-σb))) := by rw [hχA, hχB]
      _ = (χ (∏ l : Fin 3, F l) * (starRingEnd ℂ) (χ (∏ l : Fin 3, G l)))
            * (χ (thetaTwo e m σa) * χ (thetaTwo e m (-σb))) := by ring
      _ = (χ (∏ l : Fin 3, F l) * (starRingEnd ℂ) (χ (∏ l : Fin 3, G l)))
            * (χ (thetaTwo e m 1)) ^ Z.val := by
            rw [← map_mul, ← thetaTwo_add hm he h3,
              thetaTwo_of_castHom_eq hm he h3 h2 (σa + -σb) Z hzcast, map_pow]
      _ = (χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((a l : ℕ) : ZMod (2 ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, ((y : ZMod (2 ^ e)) + ((b l : ℕ) : ZMod (2 ^ e))))))
            * (χ (thetaTwo e m 1)) ^ Z.val := by rw [← hconstA, ← hconstB]
  rw [Finset.sum_congr rfl (fun w (_ : w ∈ (Finset.univ : Finset (ZMod (2 ^ (e - m))))) => hpt w)]
  exact (Finset.mul_sum Finset.univ _ _).symm


end Work.ZeroFreeTables.P9F.TwoPowAux

namespace Work.ZeroFreeTables.P9F

open Work.LinnikBurgess
open Work.ZeroFreeTables.P9F.TwoPowAux

/-- **The two-digit peel for the cubic correlation at `p = 2`** (statement of
`Work.LinnikBurgess.twoPow_innerSum_factor`, re-proved here in the `gaussSum` bubble).
For `e ≥ 3`, `m ≥ 1` with `e + 1 ≤ 3m` and `2m ≤ e`, `χ` primitive mod `2^e`, and all six shifts
`y + a_l`, `y + b_l` odd, the correlation summand at `x = y + 2^m w` factors as a `w`-independent
constant times the quadratic phase `(χ (thetaTwo e m 1)) ^ ((α w - 2^(m-1) γ w²).val)`, with
`α = defect1 2 e a b y`, `γ = defect2 2 e a b y`; and `χ (thetaTwo e m 1)` is a primitive
`2^(e-m)`-th root of unity. -/
theorem twoPow_innerSum_factor_aux {e m : ℕ} (hm : 1 ≤ m) (he : 3 ≤ e) (h3 : e + 1 ≤ 3 * m)
    (h2 : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (2 ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (y : ℕ)
    (hy : UnitAt 2 y a b) :
    IsPrimitiveRoot (χ (thetaTwo e m 1)) (2 ^ (e - m)) ∧
      (∑ w : ZMod (2 ^ (e - m)),
        χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (b l : ℕ)))))
      = (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (b l : ℕ)))))
        * (∑ w : ZMod (2 ^ (e - m)),
            (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
              - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
                * ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2)).val)) :=
  TwoPowAux.twoPow_innerSum_factor_aux hm he h3 h2 χ hχ a b y hy

end Work.ZeroFreeTables.P9F
