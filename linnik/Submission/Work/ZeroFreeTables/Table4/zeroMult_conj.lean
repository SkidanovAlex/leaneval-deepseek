import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.A7.zeroMult_conj_sq_one

namespace Work.ZeroFreeTables.Table4

/-- **Conjugation symmetry of the zero multiplicity for a real (quadratic) character.**

For a Dirichlet character `χ` with `χ ^ 2 = 1` (equivalently `χ` real-valued, so that its
completed `L`-function satisfies the Schwarz reflection
`Λ(conj s) = conj (Λ s)`), the multiplicity of `conj u` as a non-trivial zero of `L(s, χ)` equals
the multiplicity of `u`:

`zeroMult χ (conj u) = zeroMult χ u`.

This is the `χ⁻¹ = χ` specialisation of the level-independent reflection identity
`zeroMult χ⁻¹ (conj ρ) = zeroMult χ ρ` (`Work.A7.zeroMult_conj_inv`), whose proof is the classical
Schwarz-reflection argument for the completed Dirichlet `L`-function. -/
theorem zeroMult_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hsq : χ ^ 2 = 1)
    (u : ℂ) : Work.LinnikContract.zeroMult χ (starRingEnd ℂ u) = Work.LinnikContract.zeroMult χ u :=
  Work.A7.zeroMult_conj_sq_one χ hsq u

end Work.ZeroFreeTables.Table4
