import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

/-- `(s - m) + m = s` for Finsupps of naturals when `m ≤ s`. -/
lemma tsub_add_cancel_of_le_finsupp {σ : Type*} {m s : σ →₀ ℕ} (h : m ≤ s) :
    (s - m) + m = s := by
  ext i
  rw [Finsupp.add_apply, Finsupp.tsub_apply]
  exact Nat.sub_add_cancel (Finsupp.le_def.mp h i)

/-- `(n + m) - m = n` for Finsupps of naturals. -/
lemma add_tsub_cancel_right_finsupp {σ : Type*} (n m : σ →₀ ℕ) :
    (n + m) - m = n := by
  ext i
  rw [Finsupp.tsub_apply, Finsupp.add_apply]
  omega

/-- `m ≤ n + m`. -/
lemma le_add_self_finsupp {σ : Type*} (n m : σ →₀ ℕ) : m ≤ n + m := by
  rw [Finsupp.le_def]
  intro i
  rw [Finsupp.add_apply]
  omega

/-- The coefficient of a single monomial image under `∂^m`. -/
lemma coeff_pderivIterMonomial {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    [DecidableEq σ] (m n s : σ →₀ ℕ) (a : R) :
    MvPolynomial.coeff n (pderivIterMonomial m s a) =
      if s = n + m then a * ∏ i : σ, (s i).descFactorial (m i) else 0 := by
  classical
  rw [pderivIterMonomial]
  by_cases h : m ≤ s
  · rw [dif_pos h, MvPolynomial.coeff_monomial]
    have hiff : (s - m = n) ↔ (s = n + m) := by
      constructor
      · intro hh
        rw [← hh]
        exact (tsub_add_cancel_of_le_finsupp h).symm
      · intro hh
        rw [hh, add_tsub_cancel_right_finsupp]
    by_cases h2 : s - m = n
    · rw [if_pos h2, if_pos (hiff.mp h2)]
    · rw [if_neg h2, if_neg (fun h3 => h2 (hiff.mpr h3))]
  · rw [dif_neg h]
    have h3 : ¬ (s = n + m) := fun hh => h (hh ▸ le_add_self_finsupp n m)
    rw [MvPolynomial.coeff_zero, if_neg h3]

/-- The coefficient of the iterated partial derivative `∂^m P` at the multi-index `n`:
`coeff n (∂^m P) = (∏ i, ((n+m) i).descFactorial (m i)) * coeff (n+m) P`.  In particular
the support of `∂^m P` is contained in the translate `{m' - m : m' ∈ support P, m ≤ m'}`. -/
theorem coeff_pderivIter {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]
    (m n : σ →₀ ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.coeff n (pderivIter m P) =
      MvPolynomial.coeff (n + m) P * ∏ i : σ, ((n + m) i).descFactorial (m i) := by
  classical
  rw [pderivIter_eq_sum, MvPolynomial.coeff_sum]
  rw [Finset.sum_congr rfl (fun s _ => coeff_pderivIterMonomial m n s (P.coeff s))]
  rw [Finset.sum_ite_eq']
  by_cases h : n + m ∈ P.support
  · rw [if_pos h]
  · rw [if_neg h, MvPolynomial.notMem_support_iff.mp h, zero_mul]

end Commons.Algebra.MvPolynomial
