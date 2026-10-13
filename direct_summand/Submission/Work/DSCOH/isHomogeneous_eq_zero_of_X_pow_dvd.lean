import Mathlib
import Submission.Work.DSCOH.Basic

namespace Work.DSCOH

/-- A homogeneous polynomial of degree `e` which is divisible by `X i ^ k` with `k > e` must
vanish: every monomial occurring in `m` is divisible by `X i ^ k`, hence has `i`-th exponent
`≥ k > e`, whereas homogeneity forces total degree `e`. -/
theorem isHomogeneous_eq_zero_of_X_pow_dvd {A : Type*} [CommRing A] {n : ℕ} {i : Fin n}
    {m : Poly A n} {e k : ℕ} (hm : m ∈ homSub A n e) (hk : e < k)
    (h : (MvPolynomial.X i : Poly A n) ^ k ∣ m) : m = 0 := by
  have hm' : m.IsHomogeneous e := (MvPolynomial.mem_homogeneousSubmodule e m).mp hm
  obtain ⟨q, hq⟩ := h
  rw [MvPolynomial.eq_zero_iff]
  intro s
  by_contra hs
  -- the coefficient of `s` in `m = X i ^ k * q` vanishes unless `k ≤ s i`
  have hcoeff : m.coeff s = if k ≤ s i then q.coeff (s - Finsupp.single i k) else 0 := by
    rw [hq, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul']
    simp only [Finsupp.single_le_iff, one_mul]
  have hsi : k ≤ s i := by
    by_contra hc
    rw [hcoeff] at hs
    simp [hc] at hs
  -- homogeneity forces the total degree of `s` to be `e`, but it is at least `s i ≥ k > e`
  have hdeg : Finsupp.degree s = e := by
    by_contra hne
    exact hs (hm'.coeff_eq_zero hne)
  have hle : s i ≤ Finsupp.degree s := Finsupp.le_degree i s
  omega

end Work.DSCOH
