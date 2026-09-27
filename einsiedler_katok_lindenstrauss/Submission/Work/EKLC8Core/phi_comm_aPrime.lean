import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.aDiag_add

namespace Work.EKLC8Core

/-- Any two diagonal elements `aDiag t`, `aDiag u` of `SL₃(ℝ)` commute.

This is immediate from the additivity `aDiag (t + u) = aDiag t * aDiag u` (`aDiag_add`),
since addition of exponent vectors is commutative: `aDiag` is a homomorphism from the
abelian group `(ℝ³, +)` to the diagonal torus, so its image is abelian. -/
theorem aDiag_comm (t u : Fin 3 → ℝ) : aDiag t * aDiag u = aDiag u * aDiag t := by
  rw [← aDiag_add, ← aDiag_add]
  exact congrArg aDiag (add_comm t u)

/-- The contracting flow `φ_τ = aDiag (τ • flowExp)` and the `A'`-element
`a'_{ab}(s) = aDiag (fun i => if i = c then -2s else s)` commute: both lie in the
diagonal torus. -/
theorem phi_comm_aPrime (τ s : ℝ) (c : Fin 3) :
    phi τ * aPrime c s = aPrime c s * phi τ := by
  simp only [phi, aPrime]
  exact aDiag_comm _ _

end Work.EKLC8Core
