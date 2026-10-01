import Mathlib
import Submission.Work.ZeroFreeTables.P9F.twoPow_api
import Submission.Work.LinnikBurgess.corr6_twoPow_defs

open Work.LinnikBurgess

/-!
# The truncated exponential `thetaTwo` in `ZMod (2^e)`

`thetaTwo e m u = 1 + 2^m u + 2^(2m-1) u^2` behaves like `u ↦ 1 + 2^m u` as soon as
`3m ≥ e+1` (so that the correction terms are killed by `2^e`):

* it is multiplicative: `θ(u+v) = θ(u)θ(v)`,
* every value is a unit,
* the "two-digit" identity `1 + 2^m t = θ (t - 2^(m-1) t^2)` holds,
* `θ(1)` is a primitive `2^(e-m)`-th root of unity (after applying a primitive character
  modulo `2^e`).
-/

namespace Work.LinnikAreas.u8own

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

end Work.LinnikAreas.u8own
