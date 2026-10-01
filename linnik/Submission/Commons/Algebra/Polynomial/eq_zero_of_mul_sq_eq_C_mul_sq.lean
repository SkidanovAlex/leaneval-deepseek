import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

open _root_.Polynomial

/-- Auxiliary lemma: if `g ≠ 0` and `g * P ^ 2 = C c * Q ^ 2` with `c ≠ 0` and `P ≠ 0`,
then `g` is a constant multiple of a square of a polynomial. -/
theorem exists_C_mul_sq_of_mul_sq_eq_C_mul_sq {F : Type*} [Field F] {g P Q : Polynomial F}
    {c : F} (hc : c ≠ 0) (hg : g ≠ 0) (hP : P ≠ 0)
    (h : g * P ^ 2 = Polynomial.C c * Q ^ 2) :
    ∃ a : F, ∃ h' : Polynomial F, g = Polynomial.C a * h' ^ 2 := by
  classical
  have hQ : Q ≠ 0 := by
    intro h0
    have h' : g * P ^ 2 = 0 := by rw [h, h0]; ring
    rcases mul_eq_zero.mp h' with hg0 | hP2
    · exact hg hg0
    · exact hP (sq_eq_zero_iff.mp hP2)
  let p := P / gcd P Q
  let q := Q / gcd P Q
  have hdne : gcd P Q ≠ 0 := gcd_ne_zero_of_left hP
  have hcop : IsCoprime p q := isCoprime_div_gcd_div_gcd (p := P) (q := Q) hQ
  have hPm : gcd P Q * p = P := EuclideanDomain.mul_div_cancel' hdne (gcd_dvd_left P Q)
  have hQm : gcd P Q * q = Q := EuclideanDomain.mul_div_cancel' hdne (gcd_dvd_right P Q)
  have hpne : p ≠ 0 := left_div_gcd_ne_zero (p := P) (q := Q) hP
  have h2 : g * p ^ 2 = Polynomial.C c * q ^ 2 := by
    have key : (gcd P Q) ^ 2 * (g * p ^ 2) = (gcd P Q) ^ 2 * (Polynomial.C c * q ^ 2) := by
      calc (gcd P Q) ^ 2 * (g * p ^ 2)
          = g * (gcd P Q * p) ^ 2 := by ring
        _ = g * P ^ 2 := by rw [hPm]
        _ = Polynomial.C c * Q ^ 2 := h
        _ = Polynomial.C c * (gcd P Q * q) ^ 2 := by rw [hQm]
        _ = (gcd P Q) ^ 2 * (Polynomial.C c * q ^ 2) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hdne) key
  have hcop2 : IsCoprime (p ^ 2) (q ^ 2) := hcop.pow
  have hdvd : p ^ 2 ∣ Polynomial.C c * q ^ 2 := ⟨g, by rw [← h2, mul_comm]⟩
  have hdvdC : p ^ 2 ∣ Polynomial.C c := IsCoprime.dvd_of_dvd_mul_right hcop2 hdvd
  obtain ⟨t, ht⟩ := hdvdC
  have hp2ne : p ^ 2 ≠ 0 := pow_ne_zero 2 hpne
  have hgt : g = t * q ^ 2 := by
    have h4 : g * p ^ 2 = (t * q ^ 2) * p ^ 2 := by rw [h2, ht]; ring
    exact mul_right_cancel₀ hp2ne h4
  have hCne : Polynomial.C c ≠ 0 := Polynomial.C_ne_zero.mpr hc
  have htne : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    exact hCne ht
  have hdeg : t.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hp2ne htne
    rw [← ht] at hmul
    rw [Polynomial.natDegree_C] at hmul
    omega
  obtain ⟨a, ha⟩ : ∃ a : F, t = Polynomial.C a :=
    ⟨t.coeff 0, eq_C_of_natDegree_eq_zero hdeg⟩
  exact ⟨a, q, by rw [hgt, ha]⟩

/-- If `g` is not a constant multiple of a square and `g * P ^ 2 = C c * Q ^ 2` with `c ≠ 0`,
then `P = Q = 0`. -/
theorem eq_zero_of_mul_sq_eq_C_mul_sq {F : Type*} [Field F] (g P Q : Polynomial F) (c : F)
    (hc : c ≠ 0)
    (hnd : ∀ (a : F) (h : Polynomial F), g ≠ Polynomial.C a * h ^ 2)
    (h : g * P ^ 2 = Polynomial.C c * Q ^ 2) : P = 0 ∧ Q = 0 := by
  have hg : g ≠ 0 := by
    intro h0
    exact hnd 0 0 (by rw [h0]; ring)
  have hP0 : P = 0 := by
    by_contra hP
    obtain ⟨a, h', ha⟩ := exists_C_mul_sq_of_mul_sq_eq_C_mul_sq hc hg hP h
    exact hnd a h' ha
  have hQ0 : Q = 0 := by
    have h' : Polynomial.C c * Q ^ 2 = 0 := by rw [← h, hP0]; ring
    rcases mul_eq_zero.mp h' with hc0 | hQ2
    · exact absurd hc0 (Polynomial.C_ne_zero.mpr hc)
    · exact sq_eq_zero_iff.mp hQ2
  exact ⟨hP0, hQ0⟩

end Commons.Algebra.Polynomial