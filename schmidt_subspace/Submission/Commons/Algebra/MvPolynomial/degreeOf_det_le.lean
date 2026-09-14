import Mathlib

namespace Commons.Algebra.MvPolynomial


theorem degreeOf_det_le {R : Type*} [CommRing R] {σ ι : Type*} [Fintype σ] [Fintype ι]
    [DecidableEq ι] (t : σ) (A : Matrix ι ι (MvPolynomial σ R)) (d : ℕ)
    (h : ∀ i j, MvPolynomial.degreeOf t (A i j) ≤ d) :
    MvPolynomial.degreeOf t A.det ≤ Fintype.card ι * d := by
  classical
  rw [Matrix.det_apply']
  calc MvPolynomial.degreeOf t
        (∑ π : Equiv.Perm ι, ((Equiv.Perm.sign π : ℤ) : MvPolynomial σ R) * ∏ i, A (π i) i)
      ≤ (Finset.univ : Finset (Equiv.Perm ι)).sup
          (fun π => MvPolynomial.degreeOf t
            (((Equiv.Perm.sign π : ℤ) : MvPolynomial σ R) * ∏ i, A (π i) i)) :=
        MvPolynomial.degreeOf_sum_le t _ _
    _ ≤ Fintype.card ι * d := by
        apply Finset.sup_le
        intro π _
        have hsign : MvPolynomial.degreeOf t
            (((Equiv.Perm.sign π : ℤ) : MvPolynomial σ R)) = 0 := by
          have hcast : ((Equiv.Perm.sign π : ℤ) : MvPolynomial σ R) =
              MvPolynomial.C ((Equiv.Perm.sign π : ℤ) : R) := by simp
          rw [hcast]
          exact MvPolynomial.degreeOf_C _ t
        calc MvPolynomial.degreeOf t
              (((Equiv.Perm.sign π : ℤ) : MvPolynomial σ R) * ∏ i, A (π i) i)
            ≤ MvPolynomial.degreeOf t (((Equiv.Perm.sign π : ℤ) : MvPolynomial σ R))
              + MvPolynomial.degreeOf t (∏ i, A (π i) i) :=
                MvPolynomial.degreeOf_mul_le t _ _
          _ = MvPolynomial.degreeOf t (∏ i, A (π i) i) := by rw [hsign, zero_add]
          _ ≤ ∑ i, MvPolynomial.degreeOf t (A (π i) i) :=
                MvPolynomial.degreeOf_prod_le t _ _
          _ ≤ ∑ _i : ι, d := Finset.sum_le_sum (fun i _ => h (π i) i)
          _ = Fintype.card ι * d := by
                simp [Finset.sum_const, Finset.card_univ]

end Commons.Algebra.MvPolynomial
