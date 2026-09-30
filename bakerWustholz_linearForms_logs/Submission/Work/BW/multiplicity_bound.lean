import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- If a nonzero complex polynomial `Q` has, at each of the points `0, 1, …, N - 1`, all its
iterated derivatives of order `< M` vanishing, then `N * M ≤ Q.natDegree`.

Route: for each `s < N`, the vanishing of the derivatives of orders `0, …, M-1` at `s` says that
`(X - C s) ^ M ∣ Q` (use
`Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'` to get
`M - 1 < Q.rootMultiplicity s` and then `Polynomial.le_rootMultiplicity_iff`); the `N` factors
`(X - C s) ^ M` for `s = 0, …, N-1` are pairwise coprime because the `X - C s` are, so their
product — of `natDegree` `N * M` — divides `Q`, and `natDegree` is monotone under divisibility
for nonzero divisors. -/
theorem multiplicity_bound (Q : Polynomial ℂ) (hQ : Q ≠ 0) (N M : ℕ)
    (h : ∀ s : ℕ, s < N → ∀ k : ℕ, k < M → (Polynomial.derivative^[k] Q).eval (s : ℂ) = 0) :
    N * M ≤ Q.natDegree := by
  -- Step 1: each `(X - C s) ^ M` divides `Q`.
  have hdvd : ∀ s : ℕ, s < N → (X - C (s : ℂ)) ^ M ∣ Q := by
    intro s hs
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      simp
    · rw [← Polynomial.le_rootMultiplicity_iff hQ]
      have hlt : M - 1 < Q.rootMultiplicity (s : ℂ) := by
        rw [Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hQ]
        intro m hm
        exact h s hs m (by omega)
      omega
  -- Step 2: the `N` factors are pairwise coprime, so their product divides `Q`.
  have hinj : Function.Injective (fun i : Fin N => ((i : ℕ) : ℂ)) := by
    intro a b hab
    have hab' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := hab
    exact Fin.ext (by exact_mod_cast hab')
  have hpair :
      Pairwise (Function.onFun IsRelPrime fun i : Fin N => (X - C ((i : ℕ) : ℂ)) ^ M) := by
    intro i j hij
    have hc : IsCoprime (X - C ((i : ℕ) : ℂ)) (X - C ((j : ℕ) : ℂ)) :=
      (Polynomial.pairwise_coprime_X_sub_C
        (s := fun i : Fin N => ((i : ℕ) : ℂ)) hinj) hij
    exact hc.isRelPrime.pow
  have hprod : (∏ i : Fin N, (X - C ((i : ℕ) : ℂ)) ^ M) ∣ Q :=
    Fintype.prod_dvd_of_isRelPrime hpair (fun i => hdvd i i.isLt)
  -- Step 3: the product has `natDegree` `N * M`.
  have hdeg : (∏ i : Fin N, (X - C ((i : ℕ) : ℂ)) ^ M).natDegree = N * M := by
    rw [Polynomial.natDegree_prod_of_monic Finset.univ
      (fun i : Fin N => (X - C ((i : ℕ) : ℂ)) ^ M)
      (fun i _ => (Polynomial.monic_X_sub_C ((i : ℕ) : ℂ)).pow M)]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one])]
    simp
  calc N * M = (∏ i : Fin N, (X - C ((i : ℕ) : ℂ)) ^ M).natDegree := hdeg.symm
    _ ≤ Q.natDegree := Polynomial.natDegree_le_of_dvd hprod hQ

end Work.BW
