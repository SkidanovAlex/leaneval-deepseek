import Mathlib
import Submission.Work.DSG2.ChartRingDefs

/-!
# DSG2: the value of `Phi` on the monomial generators of the chart ring

We compute `Work.DSG2.Phi` on a monomial `∏ k, Yₖ ^ (w (i.succAbove k))` of
`A[Y₀,…,Y_{n-1}]`: the result is the product of the `X_{i.succAbove k}/Xᵢ`, whose value in
`Localization.Away (X i)` is the class of `∏ j, Xⱼ ^ (w j)` divided by `Xᵢ ^ (w.degree)`.

* `Work.DSG2.Phi_prod_X` : `Phi` is multiplicative, `Yₖ ↦ X_{i.succAbove k}/Xᵢ`.
* `Work.DSG2.val_e_mul_algebraMap` : `(X_{i.succAbove k}/Xᵢ) · Xᵢ = X_{i.succAbove k}`.
* `Work.DSG2.val_Phi_prod_X` : the announced computation.
-/

open MvPolynomial HomogeneousLocalization

namespace Work.DSG2

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `Phi` sends the monomial `∏ k, Yₖ ^ (a k)` to `∏ k, (X_{i.succAbove k}/Xᵢ) ^ (a k)`. -/
theorem Phi_prod_X (A : Type) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (a : Fin n → ℕ) :
    Work.DSG2.Phi A n i (∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (a k))
      = ∏ k, (Work.DSG2.e A n i k) ^ (a k) := by
  rw [Work.DSG2.Phi]
  simp only [map_prod, map_pow, MvPolynomial.eval₂Hom_X']

/-- The class of `X_{i.succAbove k}/Xᵢ` multiplied by the class of `Xᵢ` is the class of
`X_{i.succAbove k}`. -/
theorem val_e_mul_algebraMap (A : Type) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (k : Fin n) :
    (Work.DSG2.e A n i k).val *
        algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X i)
      = algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X (i.succAbove k)) := by
  rw [Work.DSG2.e, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply]
  simp only [pow_one]
  rw [IsLocalization.mk'_spec]

theorem val_Phi_prod_X (A : Type) [CommRing A] (n : ℕ) (i : Fin (n + 1))
    (w : Fin (n + 1) →₀ ℕ) :
    (Work.DSG2.Phi A n i (∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k)))).val
      = IsLocalization.mk' (M := Submonoid.powers (MvPolynomial.X i))
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j))
          ⟨(MvPolynomial.X i) ^ (w.degree), by use w.degree⟩ := by
  rw [show (Work.DSG2.Phi A n i (∏ k, (MvPolynomial.X k : MvPolynomial (Fin n) A) ^ (w (i.succAbove k))))
      = ∏ k, (Work.DSG2.e A n i k) ^ (w (i.succAbove k)) from
        Phi_prod_X A n i (fun k => w (i.succAbove k))]
  rw [show (∏ k, (Work.DSG2.e A n i k) ^ (w (i.succAbove k))).val
      = ∏ k, ((Work.DSG2.e A n i k).val) ^ (w (i.succAbove k)) from by
        rw [← HomogeneousLocalization.algebraMap_apply (𝒜 := Work.DSG2.chartGrading A n)
              (x := Submonoid.powers (MvPolynomial.X i)), map_prod]
        simp only [HomogeneousLocalization.algebraMap_apply, map_pow]]
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have hdeg : w.degree = w i + ∑ k : Fin n, w (i.succAbove k) := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succAbove]
  have hA : algebraMap (MvPolynomial (Fin (n + 1)) A)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
        (MvPolynomial.X i ^ w.degree)
      = algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X i) ^ (w i) *
        ∏ k : Fin n, (algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X i)) ^ (w (i.succAbove k)) := by
    rw [map_pow, hdeg, pow_add, ← Finset.prod_pow_eq_pow_sum]
  rw [hA]
  have hB : (∏ k : Fin n, ((Work.DSG2.e A n i k).val) ^ (w (i.succAbove k))) *
        ((algebraMap (MvPolynomial (Fin (n + 1)) A)
            (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
            (MvPolynomial.X i) ^ (w i)) *
          ∏ k : Fin n, (algebraMap (MvPolynomial (Fin (n + 1)) A)
            (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
            (MvPolynomial.X i)) ^ (w (i.succAbove k)))
      = (∏ k : Fin n, (((Work.DSG2.e A n i k).val) *
            (algebraMap (MvPolynomial (Fin (n + 1)) A)
              (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
              (MvPolynomial.X i))) ^ (w (i.succAbove k))) *
        (algebraMap (MvPolynomial (Fin (n + 1)) A)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
          (MvPolynomial.X i) ^ (w i)) := by
    rw [show (∏ k : Fin n, (((Work.DSG2.e A n i k).val) *
            (algebraMap (MvPolynomial (Fin (n + 1)) A)
              (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
              (MvPolynomial.X i))) ^ (w (i.succAbove k)))
        = (∏ k : Fin n, ((Work.DSG2.e A n i k).val) ^ (w (i.succAbove k))) *
          (∏ k : Fin n, (algebraMap (MvPolynomial (Fin (n + 1)) A)
            (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
            (MvPolynomial.X i)) ^ (w (i.succAbove k))) from by
      simp only [mul_pow]
      rw [Finset.prod_mul_distrib]]
    ring
  rw [hB]
  have hC : (∏ k : Fin n, (((Work.DSG2.e A n i k).val) *
            (algebraMap (MvPolynomial (Fin (n + 1)) A)
              (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
              (MvPolynomial.X i))) ^ (w (i.succAbove k)))
      = ∏ k : Fin n, (algebraMap (MvPolynomial (Fin (n + 1)) A)
            (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) A))
            (MvPolynomial.X (i.succAbove k))) ^ (w (i.succAbove k)) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [val_e_mul_algebraMap A n i k]
  rw [hC]
  have hP : (∏ k : Fin n,
          (MvPolynomial.X (i.succAbove k) : MvPolynomial (Fin (n + 1)) A) ^ (w (i.succAbove k))) *
        (MvPolynomial.X i) ^ (w i)
      = (∏ j : Fin (n + 1),
          (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) := by
    rw [mul_comm, ← Fin.prod_univ_succAbove
      (fun j : Fin (n + 1) => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) A) ^ (w j)) i]
  simp_rw [← map_pow]
  rw [← map_prod, ← map_mul, hP]

end Work.DSG2
