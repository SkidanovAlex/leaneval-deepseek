import Mathlib
import Submission.Work.Q44Geom.MaxDeg

namespace Work.Q44Geom

open MvPolynomial Finset

/-- The product of the highest-degree homogeneous parts of two nonzero polynomials is the
highest-degree part of their product.

The proof is a direct coefficient computation: writing both sides out with
`MvPolynomial.coeff_mul`, a pair `(x.1, x.2)` in the antidiagonal of `d` contributes
`a.coeff x.1 * b.coeff x.2` exactly when `x.1.degree = r` (equivalently `x.2.degree = s`,
because `x.1.degree + x.2.degree = d.degree = r + s`); in every other case at least one of the
two coefficients vanishes by the maximality hypotheses. -/
lemma homogeneousComponent_mul_of_maxDeg {R : Type*} [CommSemiring R]
    {a b : MvPolynomial (Fin 5) R} {r s : ℕ} (ha : IsMaxDeg r a) (hb : IsMaxDeg s b) :
    MvPolynomial.homogeneousComponent (r + s) (a * b)
      = MvPolynomial.homogeneousComponent r a * MvPolynomial.homogeneousComponent s b := by
  classical
  ext d
  rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases hd : d.degree = r + s
  · -- the degree-`(r+s)` coefficient of the product is the coefficient of the top parts
    rw [ite_eq_left hd, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [MvPolynomial.coeff_homogeneousComponent]
    have hx' : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hdeg : x.1.degree + x.2.degree = r + s := by rw [← map_add, hx', hd]
    by_cases h1 : x.1.degree = r
    · have h2 : x.2.degree = s := by omega
      rw [ite_eq_left h1, ite_eq_left h2]
    · rw [ite_eq_right h1]
      rcases lt_or_gt_of_ne h1 with hlt | hgt
      · -- `x.1.degree < r`, so `x.2.degree > s` and `b.coeff x.2 = 0`
        have h2 : s < x.2.degree := by omega
        have hb0 : b.coeff x.2 = 0 := by
          by_contra hne
          exact absurd (hb.2 x.2 (MvPolynomial.mem_support_iff.mpr hne)) (by omega)
        simp [hb0]
      · -- `r < x.1.degree`, so `a.coeff x.1 = 0`
        have ha0 : a.coeff x.1 = 0 := by
          by_contra hne
          exact absurd (ha.2 x.1 (MvPolynomial.mem_support_iff.mpr hne)) (by omega)
        simp [ha0]
  · -- no monomial of the product has degree `r + s` in this component
    rw [ite_eq_right hd, MvPolynomial.coeff_mul]
    simp only [MvPolynomial.coeff_homogeneousComponent]
    symm
    refine Finset.sum_eq_zero (fun x hx => ?_)
    have hx' : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hdeg : x.1.degree + x.2.degree = d.degree := by rw [← map_add, hx']
    by_cases h1 : x.1.degree = r
    · have h2 : ¬ x.2.degree = s := by
        intro h2s
        exact hd (by omega)
      simp [h1, h2]
    · simp [h1]

end Work.Q44Geom
