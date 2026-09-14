import Mathlib
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties

/-!
# The `ν!`-divided iterated partial derivative

The classical proof of Roth's lemma (and of Schmidt's subspace theorem) uses the *normalised*
derivatives `∂^ν P / ν!`, whose coefficients are products of the coefficients of `P` with
binomial coefficients.  Unlike the plain iterated derivative `∂^ν P`, whose coefficients carry a
factor `(n + ν)!/n!`, these have a height bound that is *linear* in the degrees of `P`
(Schmidt's "ht of derivative"): if `deg_{x_j} P ≤ r_j` then

`h(∂^ν P / ν!) ≤ h(P) + (∑_j r_j) · log 2`.

This is the normalisation used for the Wronskian determinant of the auxiliary polynomial: the
height of `det (∂^{ν_ij} P / ν_ij!)` is `k · h(P) + O(k · ∑ r_j)`, which is what the induction
can absorb.  (With the plain derivative the loss would be quadratic in `k`.)

The crucial point for the index theory is that dividing by the nonzero constant `ν!` does not
change the index; this file also records `∂^ν P = ν! · (∂^ν P / ν!)`.
-/

open scoped BigOperators

namespace Submission.Subspace

open MvPolynomial

variable {σ : Type*}

/-- The `ν!`-divided iterated partial derivative `∂^ν P / ν!`.  On a monomial it is
`∂^ν (c • X^s)/ν! = (c * ∏ i, Nat.choose (s i) (ν i)) • X^{s-ν}` if `ν ≤ s`, and `0` otherwise;
in particular it maps polynomials with coefficients in a commutative ring into themselves. -/
noncomputable def pderivIterDiv {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m : σ →₀ ℕ) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ s ∈ P.support,
    if m ≤ s then
      MvPolynomial.monomial (s - m) (P.coeff s * ∏ i : σ, Nat.choose (s i) (m i))
    else 0

section Coeff

variable {R : Type*} [CommSemiring R] [Fintype σ] [DecidableEq σ]

/-- Coefficient of a single divided monomial image. -/
private lemma coeff_pderivIterDivMonomial (m n s : σ →₀ ℕ) (a : R) :
    MvPolynomial.coeff n (if m ≤ s then
        MvPolynomial.monomial (s - m) (a * ∏ i : σ, Nat.choose (s i) (m i)) else 0) =
      if s = n + m then a * ∏ i : σ, Nat.choose (s i) (m i) else 0 := by
  classical
  by_cases h : m ≤ s
  · rw [if_pos h, MvPolynomial.coeff_monomial]
    have hiff : (s - m = n) ↔ (s = n + m) := by
      constructor
      · intro hh
        rw [← hh]
        exact (Commons.Algebra.MvPolynomial.tsub_add_cancel_of_le_finsupp h).symm
      · intro hh
        rw [hh, Commons.Algebra.MvPolynomial.add_tsub_cancel_right_finsupp]
    by_cases h2 : s - m = n
    · rw [if_pos h2, if_pos (hiff.mp h2)]
    · rw [if_neg h2, if_neg (fun h3 => h2 (hiff.mpr h3))]
  · rw [if_neg h]
    have h3 : ¬ (s = n + m) :=
      fun hh => h (hh ▸ Commons.Algebra.MvPolynomial.le_add_self_finsupp n m)
    rw [MvPolynomial.coeff_zero, if_neg h3]

/-- **Coefficient formula for the divided iterated derivative**:
`coeff n (∂^m P / m!) = coeff (n + m) P * ∏ i, ((n+m) i).choose (m i)`. -/
theorem coeff_pderivIterDiv (m n : σ →₀ ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.coeff n (pderivIterDiv m P) =
      MvPolynomial.coeff (n + m) P * ∏ i : σ, Nat.choose ((n + m) i) (m i) := by
  classical
  rw [pderivIterDiv]
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_congr rfl (fun s _ => coeff_pderivIterDivMonomial m n s (P.coeff s))]
  rw [Finset.sum_ite_eq']
  by_cases h : n + m ∈ P.support
  · rw [if_pos h]
  · rw [if_neg h, MvPolynomial.notMem_support_iff.mp h, zero_mul]

end Coeff

section Basic

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Fintype σ] [DecidableEq σ]

@[simp]
lemma pderivIterDiv_zero (m : σ →₀ ℕ) : pderivIterDiv m (0 : MvPolynomial σ R) = 0 := by
  rw [pderivIterDiv]
  simp

/-- The divided derivative is compatible with coefficient change of rings. -/
lemma pderivIterDiv_map (φ : R →+* S) (m : σ →₀ ℕ) (P : MvPolynomial σ R) :
    pderivIterDiv m (P.map φ) = (pderivIterDiv m P).map φ := by
  classical
  ext n
  rw [coeff_pderivIterDiv, MvPolynomial.coeff_map, MvPolynomial.coeff_map, coeff_pderivIterDiv,
    map_mul, map_natCast]

end Basic

section Degree

variable {R : Type*} [CommSemiring R] [Fintype σ] [DecidableEq σ]

/-- The support of the divided derivative is contained in `{s - ν : s ∈ supp P}`, so it inherits
degree bounds. -/
lemma support_pderivIterDiv_degree_le (ν : σ →₀ ℕ) (P : MvPolynomial σ R) (r : σ → ℕ)
    (h : ∀ t ∈ P.support, ∀ j, t j ≤ r j) :
    ∀ t ∈ (pderivIterDiv ν P).support, ∀ j, t j ≤ r j := by
  classical
  intro t ht j
  rw [MvPolynomial.mem_support_iff, coeff_pderivIterDiv] at ht
  by_contra hlt
  push_neg at hlt
  have hnot : t + ν ∉ P.support := by
    intro hmem
    exact absurd (h (t + ν) hmem j) (by rw [Finsupp.add_apply]; omega)
  rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul] at ht
  exact ht rfl

/-- The `x_j`-degree does not increase under the divided derivative. -/
lemma degreeOf_pderivIterDiv_le (ν : σ →₀ ℕ) (P : MvPolynomial σ R) (j : σ) :
    MvPolynomial.degreeOf j (pderivIterDiv ν P) ≤ MvPolynomial.degreeOf j P := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_pderivIterDiv] at hm
  have h1 : MvPolynomial.coeff (m + ν) P ≠ 0 := fun h0 => hm (by rw [h0, zero_mul])
  have h2 : m j + ν j ≤ MvPolynomial.degreeOf j P := by
    have := MvPolynomial.degreeOf_le_iff.mp (le_refl (MvPolynomial.degreeOf j P)) (m + ν)
      (MvPolynomial.mem_support_iff.mpr h1)
    simpa using this
  omega

end Degree

section Field

variable {K : Type*} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]

/-- The product of factorials `ν! = ∏ i, (ν i)!`. -/
noncomputable def facOf (ν : σ →₀ ℕ) : ℕ := ∏ i : σ, (ν i).factorial

/-- `∂^ν P = ν! · (∂^ν P / ν!)` (with the scalar written on the left). -/
theorem natCast_facOf_mul_pderivIterDiv (ν : σ →₀ ℕ) (P : MvPolynomial σ K) :
    MvPolynomial.C ((facOf ν : ℕ) : K) * pderivIterDiv ν P =
      Commons.Algebra.MvPolynomial.pderivIter ν P := by
  classical
  ext n
  rw [MvPolynomial.coeff_C_mul, coeff_pderivIterDiv,
    Commons.Algebra.MvPolynomial.coeff_pderivIter]
  have hprod : ((facOf ν : ℕ) : K) *
        (∏ i : σ, ((Nat.choose ((n + ν) i) (ν i) : ℕ) : K)) =
      ∏ i : σ, ((((n + ν) i).descFactorial (ν i) : ℕ) : K) := by
    rw [facOf, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Nat.cast_mul, Nat.descFactorial_eq_factorial_mul_choose]
  have key := congrArg (fun x : K => MvPolynomial.coeff (n + ν) P * x) hprod
  simp only [Nat.cast_prod]
  rw [← key]
  ring

/-- Over a field the divided derivative is the plain iterated derivative divided by `ν!`. -/
theorem pderivIterDiv_eq_inv_mul (ν : σ →₀ ℕ) (P : MvPolynomial σ K) :
    pderivIterDiv ν P =
      MvPolynomial.C (((facOf ν : ℕ) : K)⁻¹) *
        Commons.Algebra.MvPolynomial.pderivIter ν P := by
  have hne : (((facOf ν : ℕ) : K)) ≠ 0 := by
    have : 0 < facOf ν := by
      rw [facOf]
      exact Finset.prod_pos fun i _ => Nat.factorial_pos _
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have h := natCast_facOf_mul_pderivIterDiv ν P
  rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]

end Field

end Submission.Subspace
