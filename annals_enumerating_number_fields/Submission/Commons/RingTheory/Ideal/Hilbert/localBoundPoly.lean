import Mathlib
import Submission.Commons.Algebra.Polynomial.coeff_comp_X_sub_C
import Submission.Commons.RingTheory.Ideal.Hilbert.sum_coeff_le_coeff_hilbertPoly

namespace Commons.RingTheory.Ideal.Hilbert

/-- The `(n-1)`-st coefficient of `(X - C c)^n` is `-n*c`. -/
theorem coeff_X_sub_C_pow_pred {R : Type*} [CommRing R] (c : R) :
    ∀ {n : ℕ}, 1 ≤ n → ((Polynomial.X - Polynomial.C c) ^ n).coeff (n - 1) = -((n : R) * c) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp
    · have hkey := Polynomial.coeff_mul_X_sub_C
        (p := (Polynomial.X - Polynomial.C c) ^ n) (r := c) (a := n - 1)
      rw [show n - 1 + 1 = n from by omega] at hkey
      rw [show ((Polynomial.X - Polynomial.C c) ^ (n + 1))
            = (Polynomial.X - Polynomial.C c) ^ n * (Polynomial.X - Polynomial.C c)
          from pow_succ _ _]
      rw [show n + 1 - 1 = n from by omega, hkey, ih hnpos,
        Commons.Algebra.Polynomial.coeff_X_sub_C_pow_self c n]
      push_cast
      ring

/-- The `(n-1)`-st coefficient of `f.comp (X - C c)` when `f.natDegree = n ≥ 1`. -/
theorem coeff_comp_X_sub_C_pred {R : Type*} [CommRing R] (f : Polynomial R) (c : R) {n : ℕ}
    (hn : f.natDegree = n) (hn1 : 1 ≤ n) :
    (f.comp (Polynomial.X - Polynomial.C c)).coeff (n - 1)
      = f.coeff (n - 1) - (n : R) * c * f.leadingCoeff := by
  have hle : f.eraseLead.natDegree ≤ n - 1 := by
    rcases eq_or_ne f.nextCoeff 0 with h0 | h0
    · have hh := Polynomial.natDegree_eraseLead_le_of_nextCoeff_eq_zero h0
      rw [hn] at hh; omega
    · have hh := Polynomial.natDegree_eraseLead h0
      rw [hn] at hh; omega
  have hcomp := Commons.Algebra.Polynomial.coeff_comp_X_sub_C (n := n - 1) f.eraseLead c hle
  have hdecomp : f = f.eraseLead + Polynomial.C f.leadingCoeff * Polynomial.X ^ n := by
    have h := Polynomial.eraseLead_add_C_mul_X_pow f
    rw [hn] at h
    exact h.symm
  conv_lhs => rw [hdecomp, Polynomial.add_comp, Polynomial.C_mul_comp, Polynomial.X_pow_comp]
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, hcomp,
    Polynomial.eraseLead_coeff_of_ne (n - 1) (by omega), coeff_X_sub_C_pow_pred c hn1]
  ring

theorem localBoundPoly {k : Type} [Field k] {m : ℕ}
    (K : Ideal (MvPolynomial (Fin m) k))
    (hK : ∀ x ∈ K, ∀ j, MvPolynomial.homogeneousComponent j x ∈ K)
    (hq : ∀ q ∈ K.minimalPrimes, ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (P : Polynomial ℚ)
    (hP : ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map (K.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = P.eval (t : ℚ))
    (Pq : ↥(K.minimalPrimes) → Polynomial ℚ)
    (hPq : ∀ q, ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = (Pq q).eval (t : ℚ))
    (Pp : Polynomial ℚ) (Np e : ℕ) (hNp : 1 ≤ Np) (he : 0 < e)
    (hPdeg : P.natDegree = Np - 1) (hPpdeg : Pp.natDegree = Np)
    (hbez : P = Pp - Pp.comp (Polynomial.X - Polynomial.C (e : ℚ)))
    (hdeg : ∀ q, (Pq q).natDegree = Np - 1)
    [Fintype ↥(K.minimalPrimes)] :
    (∑ q : ↥(K.minimalPrimes), (Pq q).leadingCoeff * ((Pq q).natDegree).factorial) ≤
      ((e.max 1 : ℕ) : ℚ) * Pp.leadingCoeff * Np.factorial := by
  -- the sum of the degree-`(Np-1)` coefficients of the `Pq`'s is bounded by that of `P`
  have hsum := sum_coeff_le_coeff_hilbertPoly K hK hq P hP Pq hPq (Np - 1) hdeg (le_of_eq hPdeg)
  have hcoeff_lc : ∀ q : ↥(K.minimalPrimes), (Pq q).coeff (Np - 1) = (Pq q).leadingCoeff :=
    fun q => by rw [← Polynomial.coeff_natDegree, hdeg q]
  have hP_lc : P.coeff (Np - 1) = P.leadingCoeff := by
    rw [← Polynomial.coeff_natDegree, hPdeg]
  have hsum_lc : (∑ q : ↥(K.minimalPrimes), (Pq q).leadingCoeff) ≤ P.leadingCoeff := by
    rw [Finset.sum_congr rfl (fun q _ => (hcoeff_lc q).symm), hP_lc.symm]
    exact hsum
  -- the leading coefficient of `P` in terms of that of `Pp`
  have hbez_lc : P.leadingCoeff = (e : ℚ) * (Np : ℚ) * Pp.leadingCoeff := by
    have hcomp := coeff_comp_X_sub_C_pred Pp (e : ℚ) hPpdeg hNp
    rw [← Polynomial.coeff_natDegree, hPdeg, hbez, Polynomial.coeff_sub, hcomp]
    ring
  have hLHS : (∑ q : ↥(K.minimalPrimes), (Pq q).leadingCoeff * ((Pq q).natDegree).factorial)
      = (∑ q : ↥(K.minimalPrimes), (Pq q).leadingCoeff) * ((Np - 1).factorial : ℚ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun q _ => by rw [hdeg q])
  rw [hLHS]
  refine le_trans (mul_le_mul_of_nonneg_right hsum_lc (by positivity)) ?_
  rw [hbez_lc]
  have hemax : e.max 1 = e := Nat.max_eq_left (by omega)
  have hfac : Np.factorial = Np * (Np - 1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hNp]
    rw [Nat.factorial_succ, Nat.sub_add_cancel hNp]
  rw [hemax, hfac, Nat.cast_mul]
  exact le_of_eq (by ring)

end Commons.RingTheory.Ideal.Hilbert
