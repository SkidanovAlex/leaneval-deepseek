import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem esymm_mul_powSum {σ : Type*} [Fintype σ] (f : σ → ℂ) (k : ℕ) :
    (k : ℂ) * (Finset.univ.val.map f).esymm k =
      (-1 : ℂ) ^ (k + 1) *
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
          (-1 : ℂ) ^ a.1 * (Finset.univ.val.map f).esymm a.1 * (∑ i, f i ^ a.2) := by
  classical
  have h := MvPolynomial.mul_esymm_eq_sum σ ℂ k
  have h2 := congrArg (MvPolynomial.aeval f) h
  simp only [map_mul, map_sum, map_pow, map_natCast, map_neg, map_one, MvPolynomial.aeval_X,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum] at h2
  exact h2

end Work.BW
