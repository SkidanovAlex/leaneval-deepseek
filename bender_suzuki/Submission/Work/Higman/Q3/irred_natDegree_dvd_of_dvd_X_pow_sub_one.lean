import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- If an irreducible polynomial over `𝔽₂` divides `X ^ (2 ^ n - 1) - 1`, then its degree
divides `n`.

Multiplying the divisibility by `X` turns `X ^ (2 ^ n - 1) - 1` into `X ^ (2 ^ n) - X`, and the
degree of any irreducible factor of `X ^ (q ^ n) - X` over the finite field of size `q` divides
`n` (Mathlib's `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`, whose proof is the
standard theory of finite fields: the roots of `X ^ (q ^ n) - X` form the field `𝔽_{q ^ n}`). -/
theorem irred_natDegree_dvd_of_dvd_X_pow_sub_one
    (μ : Polynomial (ZMod 2)) (hirr : Irreducible μ) {n : ℕ}
    (hdiv : μ ∣ Polynomial.X ^ (2 ^ n - 1) - 1) : μ.natDegree ∣ n := by
  have hcard : Nat.card (ZMod 2) = 2 := by simp
  refine hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (k := ZMod 2) ?_
  rw [hcard]
  have hX : (Polynomial.X : Polynomial (ZMod 2)) ^ 2 ^ n - Polynomial.X
      = (Polynomial.X ^ (2 ^ n - 1) - 1) * Polynomial.X := by
    rw [sub_mul, one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow)]
  rw [hX]
  exact dvd_mul_of_dvd_left hdiv Polynomial.X

end Work.Higman.Q3
