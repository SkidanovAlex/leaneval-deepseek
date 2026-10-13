import Mathlib

namespace Work.DSM5b

/-!
# `aeval_smul_eq_algebraMap_of_totalDegree`

Let `R → A` be a commutative algebra, `u : Fin m → A`, `t : Fin m → R`, `T : R`, `e : ℕ`, and
suppose that for every variable index `j` the image of `u j` under multiplication by `T ^ e`
lies in the image of `R`:

  `T ^ e • u j = algebraMap R A (t j)`.

Then for every polynomial `C` of total degree `≤ D`, the element `T ^ (e * D) • aeval u C` of `A`
lies in the image of `R`.

The proof decomposes `C` into its monomials (`MvPolynomial.as_sum`).  For a single monomial
`monomial s c` of total degree `sd ≤ D` one computes

  `T ^ (e * D) • aeval u (monomial s c)
     = algebraMap R A (T ^ (e * (D - sd)) * c * ∏ i, t i ^ (s i))`,

using `T ^ (e * sd) = ∏ i, (T ^ e) ^ (s i)` and `(T ^ e) ^ k * (u i) ^ k = (algebraMap (t i)) ^ k`.
Summing over the support of `C` (and using that `algebraMap` commutes with finite sums) gives the
result.
-/

/-- The key computation behind the monomial lemma: the product `∏ i, (T ^ e) ^ (s i)` distributes
onto the `u i` and turns them into the `algebraMap R A (t i)` using the hypothesis
`T ^ e • u i = algebraMap R A (t i)`. -/
lemma key_prod {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {m : ℕ}
    (u : Fin m → A) (t : Fin m → R) (T : R) (e : ℕ)
    (hu : ∀ j, T ^ e • u j = algebraMap R A (t j)) (s : Fin m →₀ ℕ) :
    algebraMap R A (T ^ (e * s.sum (fun _ k => k))) * (∏ i, u i ^ (s i))
      = ∏ i, (algebraMap R A (t i)) ^ (s i) := by
  have hsd : s.sum (fun _ k => k) = ∑ i, s i := by
    rw [Finsupp.sum_fintype]; intro i; rfl
  rw [hsd]
  have hAlg : algebraMap R A (T ^ (e * ∑ i, s i)) = ∏ i, (algebraMap R A (T ^ e)) ^ (s i) := by
    rw [pow_mul, map_pow]
    rw [← Finset.prod_pow_eq_pow_sum Finset.univ s (algebraMap R A (T ^ e))]
  rw [hAlg, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← mul_pow, ← Algebra.smul_def, hu i]

/-- The statement for a single monomial: if `monomial s c` has total degree `sd ≤ D`, then
`T ^ (e * D)` times its evaluation lies in the image of `R`. -/
theorem monomial_smul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {m : ℕ}
    (u : Fin m → A) (t : Fin m → R) (T : R) (e : ℕ)
    (hu : ∀ j, T ^ e • u j = algebraMap R A (t j))
    (s : Fin m →₀ ℕ) (c : R) (D : ℕ) (hD : s.sum (fun _ k => k) ≤ D) :
    T ^ (e * D) • MvPolynomial.aeval u (MvPolynomial.monomial s c) =
      algebraMap R A (T ^ (e * (D - s.sum (fun _ k => k))) * c * ∏ i, t i ^ (s i)) := by
  have hT : T ^ (e * D) =
      T ^ (e * (D - s.sum (fun _ k => k))) * T ^ (e * s.sum (fun _ k => k)) := by
    rw [← pow_add]
    congr 1
    rw [← Nat.mul_add, Nat.sub_add_cancel hD]
  have hkey := key_prod u t T e hu s
  calc T ^ (e * D) • MvPolynomial.aeval u (MvPolynomial.monomial s c)
      = algebraMap R A (T ^ (e * D)) * (algebraMap R A c * (∏ i, u i ^ s i)) := by
          rw [MvPolynomial.aeval_monomial, Finsupp.prod_pow, Algebra.smul_def]
    _ = (algebraMap R A (T ^ (e * (D - s.sum (fun _ k => k)))) *
            algebraMap R A (T ^ (e * s.sum (fun _ k => k)))) *
          (algebraMap R A c * (∏ i, u i ^ s i)) := by
          rw [hT, map_mul]
    _ = algebraMap R A (T ^ (e * (D - s.sum (fun _ k => k)))) * algebraMap R A c *
          (algebraMap R A (T ^ (e * s.sum (fun _ k => k))) * (∏ i, u i ^ s i)) := by ring
    _ = algebraMap R A (T ^ (e * (D - s.sum (fun _ k => k)))) * algebraMap R A c *
          (∏ i, (algebraMap R A (t i)) ^ (s i)) := by rw [hkey]
    _ = algebraMap R A (T ^ (e * (D - s.sum (fun _ k => k))) * c * ∏ i, t i ^ (s i)) := by
          simp only [map_mul, map_prod, map_pow]

theorem aeval_smul_eq_algebraMap_of_totalDegree {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] {m : ℕ} (u : Fin m → A) (t : Fin m → R)
    (T : R) (e : ℕ) (hu : ∀ j, T ^ e • u j = algebraMap R A (t j))
    (C : MvPolynomial (Fin m) R) (D : ℕ) (hdeg : C.totalDegree ≤ D) :
    ∃ r : R, T ^ (e * D) • MvPolynomial.aeval u C = algebraMap R A r := by
  classical
  refine ⟨∑ s ∈ C.support, T ^ (e * (D - s.sum (fun _ k => k))) * C.coeff s *
    ∏ i, t i ^ (s i), ?_⟩
  have hC : MvPolynomial.aeval u C
      = ∑ s ∈ C.support, MvPolynomial.aeval u (MvPolynomial.monomial s (C.coeff s)) := by
    conv_lhs => rw [MvPolynomial.as_sum C]
    rw [MvPolynomial.aeval_sum]
  rw [hC, Finset.smul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact monomial_smul u t T e hu s (C.coeff s) D
    (le_trans (MvPolynomial.le_totalDegree hs) hdeg)

end Work.DSM5b
