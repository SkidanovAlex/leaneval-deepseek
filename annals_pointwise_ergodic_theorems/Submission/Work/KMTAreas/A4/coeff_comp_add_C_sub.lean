import Mathlib

namespace Work.KMTAreas.A4

open Polynomial

/-- The `(d-1)`-st coefficient of the Taylor shift `p(X + r)` when `natDegree p = d ≥ 1`:
only the terms of degree `d-1` and `d` of `p` contribute. -/
lemma coeff_comp_X_add_C_pred {R : Type*} [CommRing R] (p : R[X]) {d : ℕ}
    (hd : p.natDegree = d) (hd1 : 1 ≤ d) (r : R) :
    (p.comp (Polynomial.X + Polynomial.C r)).coeff (d - 1) =
      p.coeff (d - 1) + (d : R) * p.coeff d * r := by
  rw [← taylor_apply, taylor_coeff]
  have hdeg : (hasseDeriv (d - 1) p).natDegree ≤ 1 := by
    have h := natDegree_hasseDeriv_le p (d - 1)
    rw [hd] at h
    omega
  rw [eval_eq_sum_range' (by omega : (hasseDeriv (d - 1) p).natDegree < 2) r]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [hasseDeriv_coeff, zero_add]
  have hce : d.choose (d - 1) = d := by
    have h := Nat.choose_succ_self_right (d - 1)
    rwa [Nat.sub_add_cancel hd1] at h
  rw [Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one, pow_one,
    show 1 + (d - 1) = d by omega, hce]

/-- The leading coefficients of `p` and of its Taylor shift `p(X + r)` coincide, hence
`p - p(X + r)` drops at least one degree. -/
lemma natDegree_sub_comp_X_add_C_le {R : Type*} [CommRing R] (p : R[X]) (r : R) :
    (p - p.comp (Polynomial.X + Polynomial.C r)).natDegree ≤ p.natDegree - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have hle : p.natDegree ≤ m := by omega
  have hc : (p.comp (Polynomial.X + Polynomial.C r)).natDegree = p.natDegree := by
    rw [← taylor_apply, natDegree_taylor]
  have hl : (p.comp (Polynomial.X + Polynomial.C r)).leadingCoeff = p.leadingCoeff := by
    rw [← taylor_apply, leadingCoeff_taylor]
  rw [coeff_sub]
  rcases eq_or_lt_of_le hle with h | h
  · have h1 : p.coeff m = p.leadingCoeff := by rw [← h, coeff_natDegree]
    have h2 : (p.comp (Polynomial.X + Polynomial.C r)).coeff m = p.leadingCoeff := by
      rw [← hc.trans h, coeff_natDegree, hl]
    rw [h1, h2, sub_self]
  · rw [coeff_eq_zero_of_natDegree_lt h,
      coeff_eq_zero_of_natDegree_lt (by rw [hc]; exact h), sub_zero]

theorem coeff_comp_add_C_sub (Q : Polynomial ℤ) (d : ℕ) (hd : Q.natDegree = d) (hd1 : 1 ≤ d)
    (h : ℤ) (hh : h ≠ 0) :
    (Q - Q.comp (Polynomial.X + Polynomial.C h)).natDegree = d - 1 ∧
      ((Q - Q.comp (Polynomial.X + Polynomial.C h)).coeff (d - 1)) = -(h * (d : ℤ) * Q.coeff d) := by
  set P := Q.comp (Polynomial.X + Polynomial.C h) with hP
  have hcoeff : P.coeff (d - 1) = Q.coeff (d - 1) + (d : ℤ) * Q.coeff d * h :=
    coeff_comp_X_add_C_pred Q hd hd1 h
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hd
    omega
  have hlad : Q.coeff d ≠ 0 := by
    rw [← hd]
    exact leadingCoeff_ne_zero.mpr hQ0
  have hDcoeff : (Q - P).coeff (d - 1) = -((d : ℤ) * Q.coeff d * h) := by
    rw [coeff_sub, hcoeff]
    ring
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hDne : (Q - P).coeff (d - 1) ≠ 0 := by
    rw [hDcoeff]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hd0 hlad) hh)
  have hUpper : (Q - P).natDegree ≤ d - 1 := by
    rw [← hd]
    exact natDegree_sub_comp_X_add_C_le Q h
  have hLower : d - 1 ≤ (Q - P).natDegree := le_natDegree_of_ne_zero hDne
  refine ⟨le_antisymm hUpper hLower, ?_⟩
  rw [hDcoeff]
  ring

end Work.KMTAreas.A4
