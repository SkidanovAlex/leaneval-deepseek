import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Polynomial.Resultant.Basic

open Polynomial
open scoped BigOperators

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Polynomial

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

/-- The discriminant commutes with applying a ring homomorphism to a monic polynomial:
`discr (p.map φ) = φ (discr p)`. -/
private lemma discr_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
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

/-- The generic monic degree-`n` polynomial is monic. -/
private lemma generic_monic {F : Type*} [Field F] [DecidableEq F] (n : ℕ) :
    (X ^ n + Polynomial.ofFn n (fun i : Fin n => MvPolynomial.X i) :
        (MvPolynomial (Fin n) F)[X]).Monic := by
  have hdeg : (Polynomial.ofFn n (fun i : Fin n => MvPolynomial.X i) :
      (MvPolynomial (Fin n) F)[X]).degree < (n : WithBot ℕ) :=
    Polynomial.ofFn_degree_lt (R := MvPolynomial (Fin n) F) (n := n)
      (fun i : Fin n => MvPolynomial.X i)
  simpa using (Polynomial.monic_X_pow_add hdeg)

/-- Evaluating the generic polynomial at a coefficient vector `v` gives the monic polynomial
built from those coefficients: `map (eval v)` sends `X^i ↦ X^n + ofFn n v`. -/
private lemma generic_map_eval {F : Type*} [Field F] [DecidableEq F] (n : ℕ) (v : Fin n → F) :
    ((X ^ n + Polynomial.ofFn n (fun i : Fin n => MvPolynomial.X i) :
        (MvPolynomial (Fin n) F)[X]).map (MvPolynomial.eval v)) =
      X ^ n + Polynomial.ofFn n v := by
  ext k
  by_cases hk : k < n
  · have hkn : k ≠ n := ne_of_lt hk
    have hleft : (((X ^ n + Polynomial.ofFn n (fun i : Fin n => MvPolynomial.X i) :
        (MvPolynomial (Fin n) F)[X]).map (MvPolynomial.eval v)).coeff k) =
        (MvPolynomial.eval v) (MvPolynomial.X ⟨k, hk⟩) := by
      rw [Polynomial.coeff_map]
      congr 1
      rw [Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.ofFn_coeff_eq_val_of_lt (fun i : Fin n => MvPolynomial.X i) hk]
      simp [hkn]
    have hright : (X ^ n + Polynomial.ofFn n v).coeff k = v ⟨k, hk⟩ := by
      rw [Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.ofFn_coeff_eq_val_of_lt v hk]
      simp [hkn]
    have hstep : (MvPolynomial.eval v) (MvPolynomial.X ⟨k, hk⟩) = v ⟨k, hk⟩ := by
      rw [MvPolynomial.eval_X]
    rw [hleft, hstep, hright]
  · have hnk : n ≤ k := le_of_not_gt hk
    by_cases hkeq : k = n
    · subst k
      have hleft : (((X ^ n + Polynomial.ofFn n (fun i : Fin n => MvPolynomial.X i) :
          (MvPolynomial (Fin n) F)[X]).map (MvPolynomial.eval v)).coeff n) =
          (MvPolynomial.eval v) (1 : MvPolynomial (Fin n) F) := by
        rw [Polynomial.coeff_map]
        congr 1
        rw [Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.ofFn_coeff_eq_zero_of_ge (fun i : Fin n => MvPolynomial.X i) (le_rfl : n ≤ n)]
        simp
      have hright : (X ^ n + Polynomial.ofFn n v).coeff n = (1 : F) := by
        rw [Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.ofFn_coeff_eq_zero_of_ge v (le_rfl : n ≤ n)]
        simp
      have hstep : (MvPolynomial.eval v) (1 : MvPolynomial (Fin n) F) = (1 : F) := by
        rw [map_one]
      rw [hleft, hstep, hright]
    · have hkn : n < k := lt_of_le_of_ne hnk (Ne.symm hkeq)
      have hleft : (((X ^ n + Polynomial.ofFn n (fun i : Fin n => MvPolynomial.X i) :
          (MvPolynomial (Fin n) F)[X]).map (MvPolynomial.eval v)).coeff k) =
          (MvPolynomial.eval v) (0 : MvPolynomial (Fin n) F) := by
        rw [Polynomial.coeff_map]
        congr 1
        rw [Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.ofFn_coeff_eq_zero_of_ge (fun i : Fin n => MvPolynomial.X i) (le_of_lt hkn)]
        simp [hkeq]
      have hright : (X ^ n + Polynomial.ofFn n v).coeff k = (0 : F) := by
        rw [Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.ofFn_coeff_eq_zero_of_ge v (le_of_lt hkn)]
        simp [hkeq]
      have hstep : (MvPolynomial.eval v) (0 : MvPolynomial (Fin n) F) = (0 : F) := by
        rw [map_zero]
      rw [hleft, hstep, hright]

/-- The discriminant of the generic monic degree-`n` polynomial (whose non-leading
coefficients are variables `X i`) is a polynomial in the coefficients, and evaluating it at a
coefficient vector `v` gives the discriminant of the monic polynomial `X^n + ofFn n v` built from
those coefficients.  I.e. `discr` commutes with the evaluation ring hom `MvPolynomial.eval v`.
Used to count monic polynomials over a finite field with discriminant `≡ 0 mod p` via
Schwartz-Zippel. -/
theorem discr_coeffVector_eval {F : Type*} [Field F] [DecidableEq F] (n : ℕ) (v : Fin n → F) :
    (Polynomial.discr (X ^ n + Polynomial.ofFn n (fun i : Fin n => MvPolynomial.X i) :
        (MvPolynomial (Fin n) F)[X])).eval v =
      Polynomial.discr (X ^ n + Polynomial.ofFn n v) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [discr_one]
  · let p : (MvPolynomial (Fin n) F)[X] :=
      X ^ n + Polynomial.ofFn n (fun i : Fin n => MvPolynomial.X i)
    let φ : MvPolynomial (Fin n) F →+* F := MvPolynomial.eval v
    have hp_monic : p.Monic := by
      simpa [p] using (generic_monic (F := F) n)
    have hp_map : p.map φ = X ^ n + Polynomial.ofFn n v := by
      simpa [p, φ] using (generic_map_eval (F := F) n v)
    calc
      (Polynomial.discr p).eval v = φ (Polynomial.discr p) := rfl
      _ = Polynomial.discr (p.map φ) := (discr_map φ hp_monic).symm
      _ = Polynomial.discr (X ^ n + Polynomial.ofFn n v) := by rw [hp_map]

end Commons.FieldTheory.Polynomial