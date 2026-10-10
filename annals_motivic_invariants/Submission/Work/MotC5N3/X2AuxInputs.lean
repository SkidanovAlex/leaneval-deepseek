import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZElimData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Inputs for `X 2 ∉ √(ZIAS a b g)` (the general-`K` statement)

This module records the two inputs of the proof of `Work.MotC5N3.X2_notMem_radical_genAux`,
together with the explicit graph data `D, R` produced by the CAS
(see `Submission/Work/MotC5N3/X2_notMem_radical_genAux_NOTES.md`).

* `D`, `R`: the `X 0`-coefficient and the `X 0`-free part of the small graph element
  `G = (a^2+b^2)*zcubAS a b g 3 - (a^2-a*b-b^2)*zcubAS a b g 1 = D*X 0 + R` of `ZIAS a b g`.
* `sat_ident`: `D^(m_k) * zcubAS a b g k ∈ (P, G)` in characteristic `5`, `P = ASZElim.P`
  (the eliminant, whose membership in `ZIAS a b g` is `Work.MotAS.ASZElimMem`).
* `P_not_dvd_DX2`: the eliminand does not divide `D^j * X 2^M` for any `j, M`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false

namespace Work.MotC5N3.X2AuxInputs

open MvPolynomial

variable {K : Type*} [Field K] [CharP K 5]

/-- `X 0`-coefficient of the small graph element. -/
noncomputable def D (a b g : K) : MvPolynomial (Fin 3) K :=
  C ((1)*a^6*g)*X 1*X 2 + C ((-1)*a^6)*X 1 + C ((-2)*a^6) + C ((-3)*a^5*b*g)*X 1*X 2 + C ((1)*a^5*b)*X 1^2 + C ((2)*a^5*b)*X 1 + C ((1)*a^5*b) + C ((3)*a^4*b^2)*X 1^2 + C ((5)*a^4*b^2) + C ((5)*a^3*b^3*g)*X 1*X 2 + C ((-6)*a^3*b^3)*X 1^2 + C ((-3)*a^2*b^4)*X 1^2 + C ((-5)*a^2*b^4) + C ((-3)*a*b^5*g)*X 1*X 2 + C ((1)*a*b^5)*X 1^2 + C ((-2)*a*b^5)*X 1 + C ((1)*a*b^5) + C ((-1)*b^6*g)*X 1*X 2 + C ((-1)*b^6)*X 1 + C ((2)*b^6)

/-- `X 0`-free part of the small graph element. -/
noncomputable def R (a b g : K) : MvPolynomial (Fin 3) K :=
  C ((1)*a^6*g)*X 1^3 + C ((4)*a^6*g)*X 1*X 2^2 + C ((-2)*a^6*g)*X 2^2 + C ((-3)*a^6)*X 1*X 2 + C ((1)*a^6)*X 2 + C ((-3)*a^5*b*g)*X 1^3 + C ((-3)*a^5*b*g)*X 1*X 2^2 + C ((1)*a^5*b*g)*X 2^2 + C ((-3)*a^5*b)*X 1^2*X 2 + C ((5)*a^5*b)*X 1*X 2 + C ((3)*a^5*b)*X 2 + C ((5)*a^4*b^2*g)*X 2^2 + C ((-2)*a^4*b^2)*X 1^2*X 2 + C ((-2)*a^4*b^2)*X 1*X 2 + C ((5)*a^3*b^3*g)*X 1^3 + C ((-1)*a^3*b^3)*X 1*X 2 + C ((-5)*a^3*b^3)*X 2^3 + C ((-5)*a^2*b^4*g)*X 2^2 + C ((-2)*a^2*b^4)*X 1^2*X 2 + C ((2)*a^2*b^4)*X 1*X 2 + C ((-3)*a*b^5*g)*X 1^3 + C ((3)*a*b^5*g)*X 1*X 2^2 + C ((1)*a*b^5*g)*X 2^2 + C ((3)*a*b^5)*X 1^2*X 2 + C ((5)*a*b^5)*X 1*X 2 + C ((-3)*a*b^5)*X 2 + C ((-1)*b^6*g)*X 1^3 + C ((4)*b^6*g)*X 1*X 2^2 + C ((2)*b^6*g)*X 2^2 + C ((3)*b^6)*X 1*X 2 + C ((1)*b^6)*X 2

/-- The small graph element. -/
noncomputable def G (a b g : K) : MvPolynomial (Fin 3) K := D a b g * X 0 + R a b g

/-- The eliminant in the chart. -/
noncomputable def Pemb (a b g : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.rename Fin.succ (Work.MotAS.ASZElim.P a b g)

end Work.MotC5N3.X2AuxInputs
