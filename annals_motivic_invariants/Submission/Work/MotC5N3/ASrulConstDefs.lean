import Mathlib
import Submission.Work.MotC5N3.ASRulingMainV2Gen
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASChart2Idents

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASrulConstDefs` — the target `S = A[T][1/ε]` of the AS ruling presentation

Setup shared by `Work.MotC5N3.ASrulTheta_fwVec` (the chart identity, the single missing input of
`Work.MotC5N3.ASrulTheta_rangeClosure`) and by that range-closure proof.

* `A := ASrulA a b g = K[X₀,X₁,X₂] ⧸ √(ZIAS a b g)`, a domain under `hDZ`;
* `R := Polynomial A`, `ε := ASrulEpsA a b g = mk (kbRw a b g 4) : A`;
* `S := Localization.Away (Polynomial.C ε)`;
* `θ := ASrulTheta a b g hDZ : K[X₀,X₁,X₂] →ₐ[K] S`,
  `X_j ↦ (C (mk (kbRv (j+1)))·T + C (mk (kbRw (j+1))))·(C ε)⁻¹`.

The element `ASrulConst a b g hDZ i` is the image of `mk (X i)` in `S`.  The instance pins inside
its definition are the ones used by `ASrulTheta` (the quotient-ring `Semiring` diamond
`Ideal.Quotient.semiring` vs `Ideal.Quotient.commSemiring.toSemiring`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

open MvPolynomial

/-- The class of `X i` inside the ruling presentation's target `S = A[T][1/ε]`; the instance pins
are the ones used by `ASrulTheta`. -/
noncomputable def ASrulConst (K : Type) [Field K] (a b g : K)
    (hDZ : IsDomain (ASrulA a b g)) (i : Fin 3) :
    Localization.Away (Polynomial.C (ASrulEpsA a b g)) := by
  letI : Semiring (ASrulA a b g) := (inferInstance : CommSemiring (ASrulA a b g)).toSemiring
  exact algebraMap (Polynomial (ASrulA a b g))
    (Localization.Away (Polynomial.C (ASrulEpsA a b g)))
    (Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
      (MvPolynomial.X i)))

end Work.MotC5N3
