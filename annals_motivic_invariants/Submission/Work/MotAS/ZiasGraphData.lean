import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZElimData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission.Work.MotAS.ZiasGraphData` — the graph data of the AS residual chart ideal

`Z := ZIAS a b g` (the chart `(1,X0,X1,X2,0)` of the residual curve) contains the element

  `G := (a^2+b^2) * zcubAS a b g 3 - (a^2-a*b-b^2) * zcubAS a b g 1`,

which is *linear in `X0`* (verified symbolically and numerically; this is the element flagged in
`Submission/Work/MotAS/ASRulV2/aszSatCertAS.lean` and `NOTE_ASZGraphCert_ROUTE.md`).  Write
`G = rename Fin.succ D0 * X 0 + rename Fin.succ R` with `D0, R ∈ K[X 0, X 1]` (the two-variable
variables being `X 1` and `X 2` of the chart, as in `ASZElimData`).  The definitions below are the
explicit polynomials, obtained from the mod-5 CAS pipeline `_aszg/mod5.py`
(`(a,b)`-homogeneous of degree 6; `D0` has 17 monomials, `R` has 25).

Data verified (CAS): for every tested non-degenerate `(a,b,g) ∈ F_5^3`, with
`m = (2,3,2,3,2)`, `f_{k,j}` the `X0^j`-coefficient of `zcubAS a b g k`, and
`N_k := Σ_j f_{k,j} D0^{m_k-j} (-R)^j ∈ K[X1,X2]`:

* `P := ASZElim.P a b g` **divides** `N_k` for `k = 0..4` (pseudo-division in `X1` over
  `F_5[a,b,g]` leaves remainder 0; and `sp.grobner([P],X1,X2,modulus=5)` reduces every `N_k` to 0
  after specialising).  Hence `N_k = S_k * P` with `S_k ∈ K[X1,X2]`.

Consumers: the saturation certificate for `Z` w.r.t. the two-generator ideal
`(rename P, G)` (see `Submission/Work/MotAS/ZiasSatGraph.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K] [CharP K 5]

/-- The `X0`-coefficient of `G = (a^2+b^2) zcubAS a b g 3 - (a^2-ab-b^2) zcubAS a b g 1`
(in the two variables `X 0 = X₁`, `X 1 = X₂` of the chart). -/
noncomputable def ziasGraphD0 (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (2*b^(6 : ℕ))
    + MvPolynomial.C ((-1)*b^(6 : ℕ)) * (X 0)^(1 : ℕ)
    + MvPolynomial.C ((-1)*b^(6 : ℕ)*g^(1 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C (a^(1 : ℕ)*b^(5 : ℕ))
    + MvPolynomial.C ((-2)*a^(1 : ℕ)*b^(5 : ℕ)) * (X 0)^(1 : ℕ)
    + MvPolynomial.C (a^(1 : ℕ)*b^(5 : ℕ)) * (X 0)^(2 : ℕ)
    + MvPolynomial.C (2*a^(1 : ℕ)*b^(5 : ℕ)*g^(1 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C (2*a^(2 : ℕ)*b^(4 : ℕ)) * (X 0)^(2 : ℕ)
    + MvPolynomial.C ((-1)*a^(3 : ℕ)*b^(3 : ℕ)) * (X 0)^(2 : ℕ)
    + MvPolynomial.C ((-2)*a^(4 : ℕ)*b^(2 : ℕ)) * (X 0)^(2 : ℕ)
    + MvPolynomial.C (a^(5 : ℕ)*b^(1 : ℕ))
    + MvPolynomial.C (2*a^(5 : ℕ)*b^(1 : ℕ)) * (X 0)^(1 : ℕ)
    + MvPolynomial.C (a^(5 : ℕ)*b^(1 : ℕ)) * (X 0)^(2 : ℕ)
    + MvPolynomial.C (2*a^(5 : ℕ)*b^(1 : ℕ)*g^(1 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C ((-2)*a^(6 : ℕ))
    + MvPolynomial.C ((-1)*a^(6 : ℕ)) * (X 0)^(1 : ℕ)
    + MvPolynomial.C (a^(6 : ℕ)*g^(1 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(1 : ℕ)

/-- The `X0`-free part of `G = (a^2+b^2) zcubAS a b g 3 - (a^2-ab-b^2) zcubAS a b g 1`. -/
noncomputable def ziasGraphR (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (b^(6 : ℕ)) * (X 1)^(1 : ℕ)
    + MvPolynomial.C ((-2)*b^(6 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C (2*b^(6 : ℕ)*g^(1 : ℕ)) * (X 1)^(2 : ℕ)
    + MvPolynomial.C ((-1)*b^(6 : ℕ)*g^(1 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(2 : ℕ)
    + MvPolynomial.C ((-1)*b^(6 : ℕ)*g^(1 : ℕ)) * (X 0)^(3 : ℕ)
    + MvPolynomial.C (2*a^(1 : ℕ)*b^(5 : ℕ)) * (X 1)^(1 : ℕ)
    + MvPolynomial.C ((-2)*a^(1 : ℕ)*b^(5 : ℕ)) * (X 0)^(2 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C (a^(1 : ℕ)*b^(5 : ℕ)*g^(1 : ℕ)) * (X 1)^(2 : ℕ)
    + MvPolynomial.C ((-2)*a^(1 : ℕ)*b^(5 : ℕ)*g^(1 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(2 : ℕ)
    + MvPolynomial.C (2*a^(1 : ℕ)*b^(5 : ℕ)*g^(1 : ℕ)) * (X 0)^(3 : ℕ)
    + MvPolynomial.C (2*a^(2 : ℕ)*b^(4 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C ((-2)*a^(2 : ℕ)*b^(4 : ℕ)) * (X 0)^(2 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C ((-1)*a^(3 : ℕ)*b^(3 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C ((-2)*a^(4 : ℕ)*b^(2 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C ((-2)*a^(4 : ℕ)*b^(2 : ℕ)) * (X 0)^(2 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C ((-2)*a^(5 : ℕ)*b^(1 : ℕ)) * (X 1)^(1 : ℕ)
    + MvPolynomial.C (2*a^(5 : ℕ)*b^(1 : ℕ)) * (X 0)^(2 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C (a^(5 : ℕ)*b^(1 : ℕ)*g^(1 : ℕ)) * (X 1)^(2 : ℕ)
    + MvPolynomial.C (2*a^(5 : ℕ)*b^(1 : ℕ)*g^(1 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(2 : ℕ)
    + MvPolynomial.C (2*a^(5 : ℕ)*b^(1 : ℕ)*g^(1 : ℕ)) * (X 0)^(3 : ℕ)
    + MvPolynomial.C (a^(6 : ℕ)) * (X 1)^(1 : ℕ)
    + MvPolynomial.C (2*a^(6 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(1 : ℕ)
    + MvPolynomial.C ((-2)*a^(6 : ℕ)*g^(1 : ℕ)) * (X 1)^(2 : ℕ)
    + MvPolynomial.C ((-1)*a^(6 : ℕ)*g^(1 : ℕ)) * (X 0)^(1 : ℕ)*(X 1)^(2 : ℕ)
    + MvPolynomial.C (a^(6 : ℕ)*g^(1 : ℕ)) * (X 0)^(3 : ℕ)

end Work.MotAS
