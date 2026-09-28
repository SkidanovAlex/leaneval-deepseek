import Mathlib

namespace Work.Q44Geom

open MvPolynomial in
/-- If `r` is the least degree of a monomial occurring in `a` and `s` the least degree of a monomial occurring in `b`, then the degree-`(r+s)` homogeneous component of `a * b` is the product of the degree-`r` component of `a` and the degree-`s` component of `b`. -/
theorem homogeneousComponent_mul_of_minDeg_gen {σ : Type*} {R : Type*} [CommSemiring R]
    {a b : MvPolynomial σ R} {r s : ℕ}
    (ha : ∃ t ∈ a.support, t.degree = r) (ha' : ∀ t ∈ a.support, r ≤ t.degree)
    (hb : ∃ t ∈ b.support, t.degree = s) (hb' : ∀ t ∈ b.support, s ≤ t.degree) :
    MvPolynomial.homogeneousComponent (r + s) (a * b) =
      MvPolynomial.homogeneousComponent r a * MvPolynomial.homogeneousComponent s b := by
  classical
  refine MvPolynomial.ext _ _ fun T => ?_
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hT : T.degree = r + s
  · rw [ite_eq_left hT]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x.1 + x.2 = T := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hdeg : x.1.degree + x.2.degree = r + s := by
      rw [← hT, ← hx', map_add]
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
    by_cases h1 : a.coeff x.1 = 0
    · simp [h1]
    · by_cases h2 : b.coeff x.2 = 0
      · simp [h2]
      · have hx1 : x.1 ∈ a.support := MvPolynomial.mem_support_iff.mpr h1
        have hge1 : r ≤ x.1.degree := ha' x.1 hx1
        have hx2 : x.2 ∈ b.support := MvPolynomial.mem_support_iff.mpr h2
        have hge2 : s ≤ x.2.degree := hb' x.2 hx2
        have e1 : x.1.degree = r := by omega
        have e2 : x.2.degree = s := by omega
        rw [ite_eq_left e1, ite_eq_left e2]
  · rw [ite_eq_right hT]
    have hzero : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal T,
        (MvPolynomial.homogeneousComponent r a).coeff x.1
          * (MvPolynomial.homogeneousComponent s b).coeff x.2) = 0 := by
      rw [Finset.sum_eq_zero]
      intro x hx
      have hx' : x.1 + x.2 = T := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have hdeg : x.1.degree + x.2.degree = T.degree := by rw [← hx', map_add]
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
      by_cases h1 : x.1.degree = r
      · have h2 : x.2.degree ≠ s := by omega
        rw [ite_eq_left h1, ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    rw [hzero]

end Work.Q44Geom
