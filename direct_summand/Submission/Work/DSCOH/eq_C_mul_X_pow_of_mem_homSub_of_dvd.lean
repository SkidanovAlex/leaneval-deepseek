import Mathlib
import Submission.Work.DSCOH.Basic

namespace Work.DSCOH

/-- A homogeneous polynomial of degree `k` which is divisible by `X i ^ k` is a scalar multiple of
`X i ^ k`.

Indeed `m = X i ^ k * q`; every monomial `d` in the support of `q` gives rise to the monomial
`k·eᵢ + d` of `m`, which must have degree `k` by homogeneity, so `d.degree = 0`, i.e. `d = 0`.
Hence `q` is a constant. -/
theorem eq_C_mul_X_pow_of_mem_homSub_of_dvd {A : Type*} [CommRing A] {n : ℕ} {i : Fin n} {k : ℕ}
    {m : Poly A n} (hm : m ∈ homSub A n k) (h : (MvPolynomial.X i : Poly A n) ^ k ∣ m) :
    ∃ a : A, m = MvPolynomial.C a * (MvPolynomial.X i : Poly A n) ^ k := by
  have hm' : m.IsHomogeneous k := (MvPolynomial.mem_homogeneousSubmodule k m).mp hm
  obtain ⟨q, hq⟩ := h
  -- `q` is a constant: any monomial `d` in its support would make `k·eᵢ + d` a monomial of `m`
  -- of degree `k`, forcing `d.degree = 0`.
  have hqC : q = MvPolynomial.C (q.coeff 0) := by
    ext d
    by_cases hd : d = 0
    · subst hd; simp
    · have hzero : q.coeff d = 0 := by
        by_contra hne
        have hcoeff : m.coeff (Finsupp.single i k + d) ≠ 0 := by
          rw [hq, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul]
          simpa using hne
        have hdeg : (Finsupp.single i k + d).degree = k := by
          by_contra hne'
          exact hcoeff (hm'.coeff_eq_zero hne')
        rw [map_add, Finsupp.degree_single] at hdeg
        have : d.degree = 0 := by omega
        exact hd (Finsupp.degree_eq_zero_iff d |>.mp this)
      rw [MvPolynomial.coeff_C, ite_eq_right (Ne.symm hd), hzero]
  obtain ⟨a, ha⟩ : ∃ a : A, q = MvPolynomial.C a := ⟨q.coeff 0, hqC⟩
  exact ⟨a, by rw [hq, ha]; exact mul_comm _ _⟩

end Work.DSCOH
