import Mathlib
import Submission.Work.SynFFT.defs

/-!
# `yMul`: the `ℤ`-action of `y` on `ℂ[y]/(y^r+1)`

`HvdH.yMul r e a` is multiplication by `y^e` on the coefficient vector `a` of an element of the
synthetic ring `R = ℂ[y]/(y^r+1)`, as used by the synthetic FFT.  This file proves the basic
facts collected in `yMulFacts`: that `e ↦ yMul r e` is an action of `ℤ` (composition law,
identity), that it is `ℂ`-linear, that each coordinate of `yMul r e a` is `±` a coordinate of `a`,
and the two relations `y^r = -1`, `y^{2r} = 1` specialising that action to an action of `ℤ/2r`.

The proof rests on the explicit formula

`(yMul r e a) k = σ · vget a i`,   `i = ((k : ℤ) - e) % r`,   `σ = (-1)^{⌊((k:ℤ)-e)/r⌋}`,

i.e. multiplication by `y^e` shifts the coefficient index by `e` modulo `r` (the shift `e = r`
giving the sign `-1`), which is exactly the quotient ring relation `y^r = -1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-! ## The sign of an integer -/

/-- `sgnZ x = (-1)^x` (`= 1` for even `x`, `= -1` for odd `x`). -/
private noncomputable def sgnZ (x : ℤ) : ℂ := if Even x then 1 else -1

private lemma sgnZ_even (x : ℤ) (h : Even x) : sgnZ x = 1 := by
  simp only [sgnZ]; rw [ite_eq_left h]

private lemma sgnZ_odd (x : ℤ) (h : Odd x) : sgnZ x = -1 := by
  simp only [sgnZ]; rw [ite_eq_right (Int.not_even_iff_odd.mpr h)]

private lemma sgnZ_zero : sgnZ 0 = 1 := sgnZ_even 0 ⟨0, by norm_num⟩

/-- `(-1)^{x+y} = (-1)^x (-1)^y`. -/
private lemma sgnZ_add (x y : ℤ) : sgnZ (x + y) = sgnZ x * sgnZ y := by
  simp only [sgnZ]
  by_cases hx : Even x <;> by_cases hy : Even y
  · rw [ite_eq_left (Int.even_add.mpr (iff_of_true hx hy)), ite_eq_left hx, ite_eq_left hy]; ring
  · rw [ite_eq_right (by rw [Int.even_add]; simp [hx, hy]), ite_eq_left hx, ite_eq_right hy]; ring
  · rw [ite_eq_right (by rw [Int.even_add]; simp [hx, hy]), ite_eq_right hx, ite_eq_left hy]; ring
  · rw [ite_eq_left (Int.even_add.mpr (iff_of_false hx hy)), ite_eq_right hx, ite_eq_right hy]; ring

/-- Adding an even integer does not change the sign. -/
private lemma sgnZ_add_even (x y : ℤ) (h : Even y) : sgnZ (x + y) = sgnZ x := by
  rw [sgnZ_add, sgnZ_even y h, mul_one]

private lemma sgnZ_one_or (x : ℤ) : sgnZ x = 1 ∨ sgnZ x = -1 := by
  simp only [sgnZ]; split <;> simp

/-- `(-1)^{-x} = (-1)^x`. -/
private lemma sgnZ_neg (x : ℤ) : sgnZ (-x) = sgnZ x := by
  simp only [sgnZ]
  by_cases h : Even x
  · rw [ite_eq_left h, ite_eq_left (even_neg.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (even_neg.mp hh))]

/-- The (explicit) `if Even _ then 1 else -1` appearing in the definition of `yMul`, expressed
with `sgnZ`: here `q = i - x` is `-x/r` where `x = k - e`. -/
private lemma ite_even_eq_sgnZ (q y : ℤ) (h : q = -y) :
    (if Even q then (1:ℂ) else -1) = sgnZ y := by
  have hiff : Even q ↔ Even y := by rw [h, even_neg]
  by_cases hq : Even q
  · rw [ite_eq_left hq, sgnZ_even y (hiff.mp hq)]
  · rw [ite_eq_right hq, sgnZ_odd y (Int.not_even_iff_odd.mp (fun hy => hq (hiff.mpr hy)))]

/-! ## Integer arithmetic of `% (r:ℤ)` and `/ (r:ℤ)` -/

/-- `(x % r - x)/r = -(x/r)`: the drop from `x` to its residue is a multiple of `r`. -/
private lemma emod_sub_self_ediv (r : ℕ) (hr : 0 < r) (x : ℤ) :
    (x % (r:ℤ) - x) / (r:ℤ) = -(x / (r:ℤ)) := by
  have hR : (r:ℤ) ≠ 0 := by omega
  have h : x % (r:ℤ) - x = -(x / (r:ℤ) * (r:ℤ)) := by
    have := Int.mul_ediv_add_emod x (r:ℤ); linarith
  rw [h, Int.neg_ediv_of_dvd (dvd_mul_left (r:ℤ) (x / (r:ℤ))),
    mul_comm (x / (r:ℤ)) (r:ℤ), Int.mul_ediv_cancel_left (x / (r:ℤ)) hR]

/-- `(x - y)/r = x/r + (x % r - y)/r`. -/
private lemma ediv_sub (r : ℕ) (hr : 0 < r) (x y : ℤ) :
    (x - y) / (r:ℤ) = x / (r:ℤ) + (x % (r:ℤ) - y) / (r:ℤ) := by
  have hR : (r:ℤ) ≠ 0 := by omega
  have h : x - y = (x % (r:ℤ) - y) + (x / (r:ℤ)) * (r:ℤ) := by
    have := Int.emod_add_mul_ediv x (r:ℤ); linarith
  rw [h, Int.add_mul_ediv_right _ _ hR, add_comm]

private lemma toNat_emod_lt (r : ℕ) (hr : 0 < r) (x : ℤ) : (x % (r:ℤ)).toNat < r := by
  rw [Int.toNat_lt' hr]
  exact Int.emod_lt_of_pos x (by exact_mod_cast hr)

/-! ## The explicit formula for `yMul` -/

/-- **Explicit form of `yMul`**: multiplication by `y^e` sends the coefficient at index `k` to the
coefficient at `(k - e) mod r`, with sign `(-1)^{⌊(k-e)/r⌋}` recording the powers of `y^r = -1`. -/
private lemma yMul_eq (r : ℕ) (hr : 0 < r) (e : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r e a = fun k : Fin r =>
      sgnZ (((k:ℤ) - e) / (r:ℤ)) * HvdH.vget a (((k:ℤ) - e) % (r:ℤ)).toNat := by
  funext k
  have hq : (((k:ℤ) - e) % (r:ℤ) + e - (k:ℤ)) / (r:ℤ) = -(((k:ℤ) - e) / (r:ℤ)) := by
    rw [show ((k:ℤ) - e) % (r:ℤ) + e - (k:ℤ) = ((k:ℤ) - e) % (r:ℤ) - ((k:ℤ) - e) by ring]
    exact emod_sub_self_ediv r hr ((k:ℤ) - e)
  change (if Even ((((k:ℤ) - e) % (r:ℤ) + e - (k:ℤ)) / (r:ℤ)) then (1:ℂ) else -1) *
      HvdH.vget a (((k:ℤ) - e) % (r:ℤ)).toNat
      = sgnZ (((k:ℤ) - e) / (r:ℤ)) * HvdH.vget a (((k:ℤ) - e) % (r:ℤ)).toNat
  rw [ite_even_eq_sgnZ _ _ hq]

/-- `vget` of `yMul` at a residue `i ∈ [0,r)`. -/
private lemma vget_yMul (r : ℕ) (hr : 0 < r) (e : ℤ) (a : Fin r → ℂ) {i : ℤ}
    (hi : 0 ≤ i) (hir : i < (r:ℤ)) :
    HvdH.vget (HvdH.yMul r e a) i.toNat = sgnZ ((i - e) / (r:ℤ)) * HvdH.vget a ((i - e) % (r:ℤ)).toNat := by
  have hilt : i.toNat < r := by rw [Int.toNat_lt' hr]; exact hir
  have hcast : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi
  rw [yMul_eq r hr e a]
  simp only [HvdH.vget, hilt, dite_eq_left, hcast]

/-! ## The action laws -/

/-- `y^{e+e'} = y^e y^{e'}`: `yMul` is an action of `ℤ`. -/
private lemma yMul_add (r : ℕ) (hr : 0 < r) (e e' : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r (e + e') a = HvdH.yMul r e (HvdH.yMul r e' a) := by
  have hR : (0:ℤ) < (r:ℤ) := by exact_mod_cast hr
  funext k
  rw [yMul_eq r hr (e + e') a, yMul_eq r hr e (HvdH.yMul r e' a)]
  simp only []
  rw [vget_yMul r hr e' a (Int.emod_nonneg _ (ne_of_gt hR)) (Int.emod_lt_of_pos _ hR)]
  rw [show (k:ℤ) - (e + e') = ((k:ℤ) - e) - e' by ring]
  rw [Int.emod_sub_emod]
  rw [show (((k:ℤ) - e) - e') / (r:ℤ)
      = ((k:ℤ) - e) / (r:ℤ) + (((k:ℤ) - e) % (r:ℤ) - e') / (r:ℤ) from ediv_sub r hr _ _]
  rw [← mul_assoc, ← sgnZ_add]

private lemma vget_add {n : ℕ} (a b : Fin n → ℂ) (i : ℕ) :
    HvdH.vget (a + b) i = HvdH.vget a i + HvdH.vget b i := by
  by_cases h : i < n <;> simp [HvdH.vget, h, Pi.add_apply]

private lemma vget_smul {n : ℕ} (c : ℂ) (a : Fin n → ℂ) (i : ℕ) :
    HvdH.vget (c • a) i = c * HvdH.vget a i := by
  by_cases h : i < n <;> simp [HvdH.vget, h, Pi.smul_apply, smul_eq_mul]

private lemma yMul_add_fun (r : ℕ) (hr : 0 < r) (e : ℤ) (a b : Fin r → ℂ) :
    HvdH.yMul r e (a + b) = HvdH.yMul r e a + HvdH.yMul r e b := by
  funext k
  rw [yMul_eq r hr e (a + b), yMul_eq r hr e a, yMul_eq r hr e b]
  simp only []
  rw [vget_add, Pi.add_apply]
  ring

private lemma yMul_smul (r : ℕ) (hr : 0 < r) (e : ℤ) (c : ℂ) (a : Fin r → ℂ) :
    HvdH.yMul r e (c • a) = c • HvdH.yMul r e a := by
  funext k
  rw [yMul_eq r hr e (c • a), yMul_eq r hr e a]
  simp only []
  rw [vget_smul, Pi.smul_apply, smul_eq_mul]
  ring

private lemma yMul_zero (r : ℕ) (hr : 0 < r) (a : Fin r → ℂ) : HvdH.yMul r 0 a = a := by
  rw [yMul_eq r hr 0 a]
  funext k
  have h1 : (0:ℤ) ≤ (k:ℤ) := by positivity
  have h2 : (k:ℤ) < (r:ℤ) := by exact_mod_cast k.isLt
  have hmod : (k:ℤ) % (r:ℤ) = (k:ℤ) := Int.emod_eq_of_lt h1 h2
  have hdiv : (k:ℤ) / (r:ℤ) = 0 := Int.ediv_eq_zero_of_lt h1 h2
  rw [sub_zero, hmod, hdiv, sgnZ_zero, one_mul, Int.toNat_natCast]
  simp only [HvdH.vget, k.isLt, dite_eq_left]

/-- Every coordinate of `yMul r e a` is `±` a coordinate of `a`. -/
private lemma yMul_sign (r : ℕ) (hr : 0 < r) (e : ℤ) (a : Fin r → ℂ) (k : Fin r) :
    ∃ (s : ℂ) (j : Fin r), (s = 1 ∨ s = -1) ∧ HvdH.yMul r e a k = s * a j := by
  refine ⟨sgnZ (((k:ℤ) - e) / (r:ℤ)),
    ⟨(((k:ℤ) - e) % (r:ℤ)).toNat, toNat_emod_lt r hr _⟩, sgnZ_one_or _, ?_⟩
  rw [yMul_eq r hr e a]
  simp only [HvdH.vget, dite_eq_left (toNat_emod_lt r hr _)]

/-- `y^{e+2r} = y^e`. -/
private lemma yMul_period (r : ℕ) (hr : 0 < r) (e : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r (e + 2*(r:ℤ)) a = HvdH.yMul r e a := by
  have hR : (r:ℤ) ≠ 0 := by omega
  funext k
  rw [yMul_eq r hr (e + 2*(r:ℤ)) a, yMul_eq r hr e a]
  simp only []
  rw [show (k:ℤ) - (e + 2*(r:ℤ)) = ((k:ℤ) - e) + (-2)*(r:ℤ) by ring]
  have hmod : (((k:ℤ) - e) + (-2)*(r:ℤ)) % (r:ℤ) = ((k:ℤ) - e) % (r:ℤ) := by
    rw [mul_comm (-2) (r:ℤ)]; exact Int.add_mul_emod_self_left _ _ _
  have hdiv : (((k:ℤ) - e) + (-2)*(r:ℤ)) / (r:ℤ) = ((k:ℤ) - e) / (r:ℤ) + (-2) :=
    Int.add_mul_ediv_right _ _ hR
  rw [hmod, hdiv, sgnZ_add_even _ _ (show Even (-2) by norm_num)]

/-- `y^{2r} = 1`. -/
private lemma yMul_twoR (r : ℕ) (hr : 0 < r) (a : Fin r → ℂ) :
    HvdH.yMul r (2*(r:ℤ)) a = a := by
  rw [show (2:ℤ)*(r:ℤ) = 0 + 2*(r:ℤ) by ring, yMul_period r hr 0 a, yMul_zero r hr a]

/-- `y^r = -1`. -/
private lemma yMul_half (r : ℕ) (hr : 0 < r) (a : Fin r → ℂ) : HvdH.yMul r (r:ℤ) a = -a := by
  have hR : (r:ℤ) ≠ 0 := by omega
  funext k
  rw [yMul_eq r hr (r:ℤ) a]
  simp only []
  rw [show (k:ℤ) - (r:ℤ) = (k:ℤ) + (-1)*(r:ℤ) by ring]
  have hmod : ((k:ℤ) + (-1)*(r:ℤ)) % (r:ℤ) = (k:ℤ) % (r:ℤ) := by
    rw [mul_comm (-1) (r:ℤ)]; exact Int.add_mul_emod_self_left _ _ _
  have hdiv : ((k:ℤ) + (-1)*(r:ℤ)) / (r:ℤ) = (k:ℤ) / (r:ℤ) + (-1) :=
    Int.add_mul_ediv_right _ _ hR
  have h1 : (0:ℤ) ≤ (k:ℤ) := by positivity
  have h2 : (k:ℤ) < (r:ℤ) := by exact_mod_cast k.isLt
  have hm : (k:ℤ) % (r:ℤ) = (k:ℤ) := Int.emod_eq_of_lt h1 h2
  have hd : (k:ℤ) / (r:ℤ) = 0 := Int.ediv_eq_zero_of_lt h1 h2
  rw [hmod, hdiv, hm, hd, Int.toNat_natCast]
  have hs : sgnZ (0 + (-1)) = -1 := by
    rw [show (0:ℤ) + (-1) = -1 by norm_num]
    exact sgnZ_odd (-1) (by norm_num)
  rw [hs, Pi.neg_apply]
  simp only [HvdH.vget, k.isLt, dite_eq_left]
  ring

theorem yMulFacts (r : ℕ) (hr : 0 < r) :
    (∀ (e e' : ℤ) (a : Fin r → ℂ), HvdH.yMul r (e + e') a = HvdH.yMul r e (HvdH.yMul r e' a)) ∧
    (∀ a : Fin r → ℂ, HvdH.yMul r 0 a = a) ∧
    (∀ (e : ℤ) (a b : Fin r → ℂ), HvdH.yMul r e (a + b) = HvdH.yMul r e a + HvdH.yMul r e b) ∧
    (∀ (e : ℤ) (c : ℂ) (a : Fin r → ℂ), HvdH.yMul r e (c • a) = c • HvdH.yMul r e a) ∧
    (∀ (e : ℤ) (a : Fin r → ℂ) (k : Fin r),
      ∃ (s : ℂ) (j : Fin r), (s = 1 ∨ s = -1) ∧ HvdH.yMul r e a k = s * a j) ∧
    (∀ (e : ℤ) (a : Fin r → ℂ), HvdH.yMul r (e + 2 * (r : ℤ)) a = HvdH.yMul r e a) ∧
    (∀ a : Fin r → ℂ, HvdH.yMul r (2 * (r : ℤ)) a = a) ∧
    (∀ a : Fin r → ℂ, HvdH.yMul r (r : ℤ) a = -a) :=
  ⟨yMul_add r hr, yMul_zero r hr, yMul_add_fun r hr, yMul_smul r hr, yMul_sign r hr,
    yMul_period r hr, yMul_twoR r hr, yMul_half r hr⟩

end Work.SynFFT
