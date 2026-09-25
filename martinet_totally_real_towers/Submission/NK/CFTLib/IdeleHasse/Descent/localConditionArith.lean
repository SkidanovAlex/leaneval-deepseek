import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.auxiliaryPrimeOrder

/-!
# The arithmetic input for the local condition: a prime `q` with prescribed Frobenius order

Given a base cardinality `N ≥ 2` and `n > 0`, there is a prime `q > N` with
`n ∣ orderOf ((N : ZMod q))`.  This is the arithmetic input of the construction of the cyclic
cyclotomic level `M = K(ζ_q)`: for the local field `K_{v₀}` with residue cardinality `N`, the
cyclotomic extension `K_{v₀}(ζ_q)/K_{v₀}` is unramified of degree `orderOf (N : ZMod q)`, so that
`n = [L_{v₀} : K_{v₀}]` divides the local degree whenever `n ∣ orderOf (N : ZMod q)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace NK.CFTLib.IdeleHasse.Descent

/-- **A prime `q > N` with `n ∣ orderOf (N mod q)`.** -/
theorem exists_prime_gt_orderOf_dvd (N : ℕ) (hN : 1 < N) (n : ℕ) (hn : 0 < n) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ n ∣ orderOf ((N : ZMod q)) := by
  obtain ⟨q, hq, -, hgt, hdvd⟩ :=
    NK.CFTLib.ArtinReciprocityIdeal.auxiliaryPrimeOrder N hN n hn ∅ (by simp)
  exact ⟨q, hq, hgt, hdvd⟩

end NK.CFTLib.IdeleHasse.Descent
