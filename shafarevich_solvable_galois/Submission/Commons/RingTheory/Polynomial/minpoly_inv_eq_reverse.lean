import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Polynomial

namespace Commons.RingTheory.Polynomial

/-- Reversing a polynomial twice gives back the original polynomial, provided that
the constant coefficient is nonzero. -/
theorem reverse_reverse {R : Type*} [Semiring R] {p : R[X]} (h : p.coeff 0 ≠ 0) :
    p.reverse.reverse = p := by
  have hnt : p.natTrailingDegree = 0 := (natTrailingDegree_eq_zero).mpr (Or.inr h)
  have hnd : (reflect p.natDegree p).natDegree = p.natDegree := by
    rw [← _root_.Polynomial.reverse, reverse_natDegree, hnt, tsub_zero]
  unfold _root_.Polynomial.reverse
  rw [hnd, reflect_reflect]

/-- If the reverse of a polynomial with nonzero constant coefficient is a unit, then the
polynomial itself is a unit. -/
theorem isUnit_of_isUnit_reverse {R : Type*} [Semiring R] [NoZeroDivisors R] {p : R[X]}
    (h : p.coeff 0 ≠ 0) (hu : IsUnit p.reverse) : IsUnit p := by
  obtain ⟨r, hr, hCr⟩ := isUnit_iff.mp hu
  have hp : p = C r := by
    rw [← reverse_reverse h, ← hCr, reverse_C]
  rw [hp]
  exact isUnit_C.mpr hr

/-- The reverse of an irreducible polynomial with nonzero constant coefficient is
irreducible. -/
theorem irreducible_reverse {K : Type*} [Field K] {p : K[X]} (hp : Irreducible p)
    (h0 : p.coeff 0 ≠ 0) : Irreducible p.reverse := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  refine ⟨?_, ?_⟩
  · intro hu
    exact hp.not_isUnit (isUnit_of_isUnit_reverse h0 hu)
  · intro a b hab
    have hcoeff : a.coeff 0 * b.coeff 0 = p.leadingCoeff := by
      rw [← coeff_zero_reverse p, hab, mul_coeff_zero]
    have ha0 : a.coeff 0 ≠ 0 := fun h => hlc (by rw [← hcoeff, h, zero_mul])
    have hb0 : b.coeff 0 ≠ 0 := fun h => hlc (by rw [← hcoeff, h, mul_zero])
    have hpab : p = a.reverse * b.reverse := by
      rw [← reverse_reverse h0, hab, reverse_mul_of_domain]
    rcases hp.isUnit_or_isUnit hpab with h | h
    · exact Or.inl (isUnit_of_isUnit_reverse ha0 h)
    · exact Or.inr (isUnit_of_isUnit_reverse hb0 h)

/-- For `x ≠ 0`, the reversed minimal polynomial of `x` vanishes at `x⁻¹` exactly when
the minimal polynomial vanishes at `x`. -/
theorem aeval_inv_reverse_eq_zero_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x : L} (hx : x ≠ 0) (p : K[X]) :
    aeval x⁻¹ p.reverse = 0 ↔ aeval x p = 0 :=
  letI : Invertible x := invertibleOfNonzero hx
  (by
    rw [aeval_def, ← invOf_eq_inv x]
    exact eval₂_reverse_eq_zero_iff (algebraMap K L) x p)

theorem minpoly_inv_eq_reverse {K L : Type*} [Field K] [Field L] [Algebra K L] {x : L}
    (hx : x ≠ 0) (hxint : IsIntegral K x) :
    minpoly K x⁻¹ = Polynomial.C ((minpoly K x).coeff 0)⁻¹ * (minpoly K x).reverse := by
  set p := minpoly K x with hp_def
  have hpirr : Irreducible p := minpoly.irreducible hxint
  have hpaeval : aeval x p = 0 := minpoly.aeval K x
  have ha : p.coeff 0 ≠ 0 := by
    intro hzero
    obtain ⟨r, hr⟩ := X_dvd_iff.mpr hzero
    have hrunit : IsUnit r := (hpirr.isUnit_or_isUnit hr).resolve_left not_isUnit_X
    obtain ⟨c, hc, hCc⟩ := isUnit_iff.mp hrunit
    have hcne : c ≠ 0 := isUnit_iff_ne_zero.mp hc
    have hcmap : (algebraMap K L c) ≠ 0 := (hc.map (algebraMap K L)).ne_zero
    have hx0 : (algebraMap K L c) * x = 0 := by
      have h := hpaeval
      rw [hr, ← hCc, mul_comm (X : K[X]) (C c), aeval_mul, aeval_C, aeval_X] at h
      exact h
    rcases mul_eq_zero.mp hx0 with h | h
    · exact hcmap h
    · exact hx h
  have hnt : p.natTrailingDegree = 0 := (natTrailingDegree_eq_zero).mpr (Or.inr ha)
  have hqmonic : (C (p.coeff 0)⁻¹ * p.reverse).Monic := by
    change (C (p.coeff 0)⁻¹ * p.reverse).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff, hnt,
      inv_mul_cancel₀ ha]
  have hqroot : aeval x⁻¹ (C (p.coeff 0)⁻¹ * p.reverse) = 0 := by
    rw [aeval_mul, aeval_C, (aeval_inv_reverse_eq_zero_iff hx p).mpr hpaeval, mul_zero]
  have hqirr : Irreducible (C (p.coeff 0)⁻¹ * p.reverse) := by
    have hprirr : Irreducible p.reverse := irreducible_reverse hpirr ha
    have hassoc : Associated (C (p.coeff 0)⁻¹ * p.reverse) p.reverse :=
      associated_unit_mul_left p.reverse (C (p.coeff 0)⁻¹)
        (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero ha)))
    exact (Associated.irreducible_iff hassoc).mpr hprirr
  exact (minpoly.eq_of_irreducible_of_monic hqirr hqroot hqmonic).symm

end Commons.RingTheory.Polynomial