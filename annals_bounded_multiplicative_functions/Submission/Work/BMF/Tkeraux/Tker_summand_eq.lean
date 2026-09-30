import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.Xsum_norm_pow
import Submission.Work.BMF.Xsum_pow_defs
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.Tkeraux

/-- **Pointwise expansion of the `Tker` summand over pairs.**  For every frequency vector
`c : Fin k → ℤ`, the cast to `ℂ` of the kernel-weighted `2s`-th power of the inner sum
`Xsum k M₂ γ ε c` equals the sum over pairs of `s`-tuples of the pair weight `epsp ε p` times
the product over `j` of a single-coordinate kernel factor times an additive character, the phase
being the pair difference `dvec (j+1) p`.

This is `Work.BMF.Xsum_norm_pow` (the expansion of `‖Xsum‖^{2s}` over pairs, in the module
`Submission.Work.BMF.Xsum_norm_pow`) multiplied by the kernel prefactor `∏_j kern ...`, using
`∏_j eZ(x_j) = eZ(∑_j x_j)` (`Work.BMF.prod_eZ`) and `∏_j (a_j b_j) = (∏_j a_j)(∏_j b_j)`
(`Finset.prod_mul_distrib`); the casts are moved with `Complex.ofReal_prod` /
`Complex.ofReal_mul`.  The kernel scale `r * M₁ ^ ((j:ℕ)+1)` is a plain natural number, possibly
`0`. -/
theorem Tker_summand_eq (r s M₁ M₂ k : ℕ) (γ : Fin k → ℝ) (ε : ℕ → ℂ) (c : Fin k → ℤ) :
    (((∏ j : Fin k, kern (r * M₁ ^ ((j : ℕ) + 1)) (c j)) * ‖Xsum k M₂ γ ε c‖ ^ (2 * s) : ℝ) : ℂ)
      = ∑ p : Pair s M₂, epsp ε p * ∏ j : Fin k,
          ((kern (r * M₁ ^ ((j : ℕ) + 1)) (c j) : ℂ)
            * eZ (((c j : ℤ) : ℝ) * (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)))) := by
  -- move the real-to-complex casts inside the product and factor
  rw [Complex.ofReal_mul, Complex.ofReal_prod]
  -- expand `‖Xsum‖^{2s}` over pairs
  rw [Xsum_norm_pow]
  -- distribute the kernel prefactor over the sum over pairs
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- `∏_j (a_j · eZ(x_j)) = (∏_j a_j) · eZ(Σ_j x_j)`
  rw [Finset.prod_mul_distrib, prod_eZ]
  -- the phase `γ_j c_j dvec` is `c_j (γ_j dvec)`
  have hsum : (∑ j : Fin k, γ j * (c j : ℝ) * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))
      = ∑ j : Fin k, ((c j : ℤ) : ℝ) * (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  -- remaining rearrangement of the (now atomic) product of kernel factors
  ring

end Work.BMF.Tkeraux
