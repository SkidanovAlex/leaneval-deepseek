import Mathlib.RingTheory.Polynomial.Resultant.Basic

open Polynomial

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Polynomial

/-- `(-1)^k` is its own inverse: multiplying by it twice is the identity. -/
private lemma neg_one_sq_mul (T : Type*) [CommRing T] (k : ℕ) (x : T) :
    ((-1 : T) ^ k) * (((-1 : T) ^ k) * x) = x := by
  calc
    ((-1 : T) ^ k) * (((-1 : T) ^ k) * x) = (((-1 : T) ^ k) * (-1 : T) ^ k) * x := by
      rw [← mul_assoc]
    _ = ((-1 : T) ^ (k + k)) * x := by
      rw [← pow_add]
    _ = (((-1 : T) ^ 2) ^ k) * x := by
      rw [show k + k = 2 * k by omega, pow_mul]
    _ = (1 : T) ^ k * x := by
      rw [neg_one_sq]
    _ = x := by
      simp

/-- The discriminant of a monic polynomial of positive degree is the resultant with its
derivative, up to the usual sign. -/
private lemma discr_eq_neg_one_pow_mul_resultant_of_monic {T : Type*} [CommRing T] (f : T[X])
    (hm : f.Monic) (hf : 0 < f.degree) :
    f.discr = (-1 : T) ^ (f.natDegree * (f.natDegree - 1) / 2) *
      (f.resultant f.derivative f.natDegree (f.natDegree - 1)) := by
  let s : T := (-1 : T) ^ (f.natDegree * (f.natDegree - 1) / 2)
  have hres := Polynomial.resultant_deriv hf
  have hres' : f.resultant f.derivative f.natDegree (f.natDegree - 1) = s * f.discr := by
    simpa [s, hm.leadingCoeff] using hres
  have hs_mul : s * (f.resultant f.derivative f.natDegree (f.natDegree - 1)) = f.discr := by
    calc
      s * (f.resultant f.derivative f.natDegree (f.natDegree - 1)) =
          s * (s * f.discr) := by rw [hres']
      _ = f.discr := by
        simpa [s] using (neg_one_sq_mul T (f.natDegree * (f.natDegree - 1) / 2) f.discr)
  exact hs_mul.symm

/-- The discriminant of the polynomial `1` is `1`. -/
private lemma discr_one (T : Type*) [CommRing T] : Polynomial.discr (1 : T[X]) = 1 := by
  rw [← Polynomial.C_1 (R := T), Polynomial.discr_C]

theorem discr_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {p : R[X]} (hp : p.Monic) : Polynomial.discr (p.map φ) = φ (Polynomial.discr p) := by
  by_cases hS : Nontrivial S
  · haveI : Nontrivial S := hS
    by_cases hn : p.natDegree = 0
    · -- constant monic polynomial: p = 1
      have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
      have hc : p.coeff 0 = 1 := by
        simpa [Polynomial.leadingCoeff, hn] using hp.leadingCoeff
      have hp1 : p = 1 := by
        calc
          p = C (p.coeff 0) := hpC
          _ = C 1 := by rw [hc]
          _ = 1 := Polynomial.C_1
      rw [hp1]
      rw [Polynomial.map_one, discr_one S, discr_one R, φ.map_one]
    · -- positive-degree case
      have hnd : (p.map φ).natDegree = p.natDegree := hp.natDegree_map φ
      have hnpos : 0 < p.natDegree := Nat.pos_of_ne_zero hn
      have hpdeg : 0 < p.degree := (Polynomial.natDegree_pos_iff_degree_pos).mp hnpos
      have hqdeg : 0 < (p.map φ).degree := by
        rw [← Polynomial.natDegree_pos_iff_degree_pos]
        rw [hnd]
        exact hnpos
      have hR : p.discr =
          (-1 : R) ^ (p.natDegree * (p.natDegree - 1) / 2) *
            (p.resultant p.derivative p.natDegree (p.natDegree - 1)) :=
        discr_eq_neg_one_pow_mul_resultant_of_monic p hp hpdeg
      have hS' : (p.map φ).discr =
          (-1 : S) ^ ((p.map φ).natDegree * ((p.map φ).natDegree - 1) / 2) *
            ((p.map φ).resultant (p.map φ).derivative (p.map φ).natDegree
              ((p.map φ).natDegree - 1)) :=
        discr_eq_neg_one_pow_mul_resultant_of_monic (p.map φ) (Polynomial.Monic.map φ hp) hqdeg
      have hφneg : φ (-1 : R) = (-1 : S) := by rw [map_neg, map_one]
      have hφs : φ ((-1 : R) ^ (p.natDegree * (p.natDegree - 1) / 2)) =
          (-1 : S) ^ (p.natDegree * (p.natDegree - 1) / 2) := by
        rw [map_pow, hφneg]
      calc
        (p.map φ).discr =
            (-1 : S) ^ ((p.map φ).natDegree * ((p.map φ).natDegree - 1) / 2) *
              ((p.map φ).resultant (p.map φ).derivative (p.map φ).natDegree
                ((p.map φ).natDegree - 1)) := hS'
        _ = (-1 : S) ^ (p.natDegree * (p.natDegree - 1) / 2) *
              ((p.map φ).resultant (p.map φ).derivative p.natDegree (p.natDegree - 1)) := by
            rw [hnd]
        _ = (-1 : S) ^ (p.natDegree * (p.natDegree - 1) / 2) *
              ((p.map φ).resultant (p.derivative.map φ) p.natDegree (p.natDegree - 1)) := by
            rw [Polynomial.derivative_map]
        _ = φ ((-1 : R) ^ (p.natDegree * (p.natDegree - 1) / 2) *
              (p.resultant p.derivative p.natDegree (p.natDegree - 1))) := by
            rw [Polynomial.resultant_map_map p p.derivative p.natDegree (p.natDegree - 1) φ]
            rw [map_mul]
            rw [hφs]
        _ = φ p.discr := by rw [hR]
  · -- S is a subsingleton ring; both sides are elements of S
    haveI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    exact Subsingleton.elim _ _

end Commons.RingTheory.Polynomial