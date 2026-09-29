import Mathlib
import Submission.Work.SynFFT.defs

/-!
# Multiplicativity of `yMul` in the exponent

`HvdH.yMul r e a` is multiplication by `y ^ e` in `ℂ[y]/(y^r+1)` on coefficient vectors
(`Submission/HvdH/Interfaces.lean`).  Here we prove that the exponent is additive:

`yMul r (e + e') a = yMul r e (yMul r e' a)`   (`r > 0`).

The proof rests on a closed description of one application of `yMul`: writing `k : Fin r`,
the coefficient picked out is `(k - e) % r` and the sign is `(-1) ^ ((k - e) / r)`
(the exponent `(k-e)/r` counts how many times `y^r = -1` is used).
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-- The index of the source coefficient: `yMul r e a k` uses `a ((k - e) % r)`. -/
def yMulIdx (r : ℕ) (e : ℤ) (k : Fin r) : ℤ := ((k : ℤ) - e) % (r : ℤ)

/-- The sign exponent: `yMul r e a k = (-1) ^ (yMulQnt r e k) • a (yMulIdx r e k)`. -/
def yMulQnt (r : ℕ) (e : ℤ) (k : Fin r) : ℤ := ((k : ℤ) - e) / (r : ℤ)

lemma yMulIdx_nonneg (r : ℕ) (hr : 0 < r) (e : ℤ) (k : Fin r) : 0 ≤ yMulIdx r e k :=
  Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt hr))

lemma yMulIdx_lt (r : ℕ) (hr : 0 < r) (e : ℤ) (k : Fin r) : yMulIdx r e k < (r : ℤ) :=
  Int.emod_lt_of_pos _ (by exact_mod_cast hr)

lemma yMulIdx_toNat_lt (r : ℕ) (hr : 0 < r) (e : ℤ) (k : Fin r) :
    (yMulIdx r e k).toNat < r :=
  (Int.toNat_lt (yMulIdx_nonneg r hr e k)).2 (yMulIdx_lt r hr e k)

lemma yMulIdx_toNat_cast (r : ℕ) (hr : 0 < r) (e : ℤ) (k : Fin r) :
    ((yMulIdx r e k).toNat : ℤ) = yMulIdx r e k :=
  Int.toNat_of_nonneg (yMulIdx_nonneg r hr e k)

/-- The `ℤ`-value of the `Fin r` index `⟨(yMulIdx r e k).toNat, _⟩`. -/
lemma yMulIdx_fin_cast (r : ℕ) (hr : 0 < r) (e : ℤ) (k : Fin r) :
    ((⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩ : Fin r) : ℤ)
      = ((k : ℤ) - e) % (r : ℤ) := by
  rw [yMulIdx_toNat_cast r hr e k]
  rfl

/-- Closed form of one application of `yMul`. -/
lemma yMul_apply (r : ℕ) (hr : 0 < r) (e : ℤ) (a : Fin r → ℂ) (k : Fin r) :
    HvdH.yMul r e a k
      = (-1 : ℂ) ^ yMulQnt r e k * a ⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩ := by
  have hrv : (r : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hq : (yMulIdx r e k + e - (k : ℤ)) / (r : ℤ) = - yMulQnt r e k := by
    have h1 : yMulIdx r e k + (r : ℤ) * yMulQnt r e k = (k : ℤ) - e :=
      Int.emod_add_mul_ediv _ _
    have h2 : yMulIdx r e k + e - (k : ℤ) = (r : ℤ) * (-(yMulQnt r e k)) := by linarith
    rw [h2, Int.mul_ediv_cancel_left _ hrv]
  have hsign : (if Even ((yMulIdx r e k + e - (k : ℤ)) / (r : ℤ)) then (1 : ℂ) else -1)
      = (-1 : ℂ) ^ yMulQnt r e k := by
    rw [hq, neg_one_zpow_eq_ite]
    simp only [even_neg]
  have hv : HvdH.vget a (yMulIdx r e k).toNat
      = a ⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩ := by
    rw [HvdH.vget, dite_eq_left (yMulIdx_toNat_lt r hr e k)]
  simp only [HvdH.yMul]
  rw [show ((k : ℤ) - e) % (r : ℤ) = yMulIdx r e k from rfl, hsign, hv]

/-- Euclidean division step: decreasing the dividend by `y` first reduces the remainder. -/
lemma emod_sub_step (r x y : ℤ) : (x - y) % r = ((x % r) - y) % r := by
  have h1 : (x - y) % r = (x % r - y % r) % r := Int.sub_emod x y r
  have h2 : ((x % r) - y) % r = ((x % r) % r - y % r) % r := Int.sub_emod (x % r) y r
  rw [h1, h2, Int.emod_emod]

/-- Euclidean division step: the quotient of `x - y` splits off the quotient of `x`. -/
lemma ediv_sub_step (r : ℤ) (hr : r ≠ 0) (x y : ℤ) :
    (x - y) / r = x / r + (x % r - y) / r := by
  have h : x - y = (x % r - y) + r * (x / r) := by
    have := Int.mul_ediv_add_emod x r
    linarith
  rw [h, Int.add_mul_ediv_left _ _ hr]
  ring

/-- The index transforms contravariantly under addition of exponents. -/
lemma yMulIdx_add (r : ℕ) (hr : 0 < r) (e e' : ℤ) (k : Fin r) :
    yMulIdx r (e + e') k = yMulIdx r e' ⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩ := by
  show (((k : ℤ) - (e + e')) % (r : ℤ)) = _
  rw [show (k : ℤ) - (e + e') = ((k : ℤ) - e) - e' by ring]
  rw [emod_sub_step (r : ℤ) ((k : ℤ) - e) e']
  show (((k : ℤ) - e) % (r : ℤ) - e') % (r : ℤ)
      = (↑(⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩ : Fin r) - e') % (r : ℤ)
  rw [yMulIdx_fin_cast r hr e k]

/-- The sign exponent is additive. -/
lemma yMulQnt_add (r : ℕ) (hr : 0 < r) (e e' : ℤ) (k : Fin r) :
    yMulQnt r (e + e') k
      = yMulQnt r e k + yMulQnt r e' ⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩ := by
  have hrv : (r : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  show (((k : ℤ) - (e + e')) / (r : ℤ)) = _
  rw [show (k : ℤ) - (e + e') = ((k : ℤ) - e) - e' by ring]
  rw [ediv_sub_step (r : ℤ) hrv ((k : ℤ) - e) e']
  show ((k : ℤ) - e) / (r : ℤ) + (((k : ℤ) - e) % (r : ℤ) - e') / (r : ℤ)
      = ((k : ℤ) - e) / (r : ℤ)
        + (↑(⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩ : Fin r) - e') / (r : ℤ)
  rw [yMulIdx_fin_cast r hr e k]

theorem yMulExpAdd (r : ℕ) (hr : 0 < r) (e e' : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r (e + e') a = HvdH.yMul r e (HvdH.yMul r e' a) := by
  funext k
  rw [yMul_apply r hr (e + e') a k, yMul_apply r hr e (HvdH.yMul r e' a) k,
      yMul_apply r hr e' a ⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩]
  have hFin : (⟨(yMulIdx r (e + e') k).toNat, yMulIdx_toNat_lt r hr (e + e') k⟩ : Fin r)
      = ⟨(yMulIdx r e' ⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩).toNat,
         yMulIdx_toNat_lt r hr e' ⟨(yMulIdx r e k).toNat, yMulIdx_toNat_lt r hr e k⟩⟩ :=
    Fin.ext (congrArg Int.toNat (yMulIdx_add r hr e e' k))
  rw [hFin, yMulQnt_add r hr e e' k]
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  ring

end Work.SynFFT
