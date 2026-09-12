import Mathlib
import Submission.Commons.Algebra.MvPolynomial.exists_harmonic_orthonormal_basis
import Submission.Commons.Algebra.MvPolynomial.finrank_harmHom_add
import Submission.Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule
import Submission.Commons.Algebra.Binomial.harmonic_dim_arith

namespace Commons.Algebra.MvPolynomial

set_option linter.style.haveILetI false

/-- The dimension of the space of harmonic homogeneous polynomials of degree `k`
in `n ≥ 2` variables is at most `2 n^(n-2) (k+1)^(n-2)`. -/
theorem harmHom_finrank_le {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) :
    (Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k) : ℝ)
      ≤ 2 * (n : ℝ) ^ (n - 2) * ((k : ℝ) + 1) ^ (n - 2) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  -- The rank identity `finrank (harmHom n k) + finrank V_{k-2} = finrank V_k`.
  have hd := finrank_harmHom_add n k hk
  rw [finrank_homogeneousSubmodule, finrank_homogeneousSubmodule] at hd
  have hC1 : n + (k - 2) - 1 = n + k - 3 := by omega
  rw [hC1] at hd
  have hle : Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k)
      = (n + k - 1).choose k - (n + k - 3).choose (k - 2) := by omega
  rw [hle]
  exact Commons.Algebra.Binomial.harmonic_dim_arith n k hn hk

end Commons.Algebra.MvPolynomial
