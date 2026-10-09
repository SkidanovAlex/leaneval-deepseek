import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.NK.LocalInputs.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The classical value of `ε` in the local Euler characteristic at a finite place

For a number field `k`, a finite place `A` of `Ω ⊇ k` (over the rational prime `p_0`) and a
coefficient prime `p`, the local Euler characteristic of `D_A` with `𝔽_p`-coefficients reads

  `dim H¹(D_A, M) = dim H⁰(D_A, M) + dim H²(D_A, M) + ε · dim M`,

with the constant `ε` equal to `0` when `p` is not the residue characteristic of `A` and equal to
the local degree `[k_v : ℚ_p]` when `p` is the residue characteristic of `A`
(Milne, *Arithmetic Duality Theorems*, I.2.8; NSW 7.3.1).

`localEulerEps p k Ω A hA` is that number.  It is the `ε` of
`Work.SSGRoute.local_tate_duality_euler`.
-/

open scoped Pointwise

namespace Work.SSGRoute

noncomputable section

/-- The constant `ε` of the local Euler characteristic at the finite place `A`: `0` if `p` is not
the residue characteristic of `A` (equivalently `A.valuation p = 1`), and the local degree
`[k_v : ℚ_p]` if it is. -/
def localEulerEps (p : ℕ) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : ℕ :=
  if A.valuation ((p : ℚ) : Ω) < 1 then
    NK.LocalInputs.localDegree k (Submission.NeukirchUchida.primeOf A hA) else 0

@[simp] theorem localEulerEps_of_residueChar (p : ℕ) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : A.valuation ((p : ℚ) : Ω) < 1) :
    localEulerEps p k Ω A hA = NK.LocalInputs.localDegree k
      (Submission.NeukirchUchida.primeOf A hA) := by
  rw [localEulerEps, if_pos h]

@[simp] theorem localEulerEps_of_not_residueChar (p : ℕ) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) : localEulerEps p k Ω A hA = 0 := by
  rw [localEulerEps, if_neg h]

end

end Work.SSGRoute
