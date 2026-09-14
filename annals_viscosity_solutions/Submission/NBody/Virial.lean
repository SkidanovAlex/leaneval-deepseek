import ChallengeDeps
import Submission.NBody.Asymptotic
import Mathlib

/-!
# The virial identity: Euler homogeneity of the Newtonian potential

Ninth stone, first lemma of the virial (Lagrange–Jacobi) route to identifying the energy first
integral with the prescribed level `h`.

`U m` is homogeneous of degree `-1`; equivalently, by Euler's theorem for homogeneous functions,

    `∑ᵢ ⟨xᵢ, (∇(U m) x)ᵢ⟩ = - U(x)`   on every collision-free configuration `x`.

The proof is short given `gradient_U_coord`: the left-hand side is `⟨∇(U m) x, x⟩
= (fderiv (U m) x) x`, and evaluating the pair-sum derivative at the direction `x` gives, for
each pair `i < j`, `mᵢmⱼ (-⟨xᵢ - xⱼ, xᵢ - xⱼ⟩/rᵢⱼ³) = -mᵢmⱼ rᵢⱼ⁻¹`, which sums to `-U(x)`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators
open InnerProductSpace

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Euler homogeneity of the Newtonian potential.**  On every collision-free configuration,
`∑ᵢ ⟨xᵢ, (∇(U m) x)ᵢ⟩ = - U(x)`. -/
theorem euler_homogeneity_U (m : Fin N → ℝ) (x : EN E N) (hx : WithoutCollisions x) :
    ∑ k : Fin N, inner ℝ (x k) ((gradient (U m) x) k) = - U m x := by
  have h1 : (∑ k : Fin N, inner ℝ (x k) ((gradient (U m) x) k))
      = ∑ k : Fin N, inner ℝ ((gradient (U m) x) k) (x k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_comm]
  rw [h1, ← PiLp.inner_apply, inner_gradient_eq_fderiv, fderiv_U_pair_apply m x x hx,
    U_eq_pairFinset, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 < p.2 := by simpa [pairFinset] using hp
  have hz : ‖x p.1 - x p.2‖ ≠ 0 := by
    have hne := hx p.1 p.2 (ne_of_lt hp')
    rwa [r_eq_norm_sub] at hne
  rw [real_inner_self_eq_norm_sq, r_eq_norm_sub]
  field_simp

end Submission.NBody
