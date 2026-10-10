import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The AS source ruling data in the base chart `{c₃ = 1, c₄ = 0}`

The AS ruling matrix `Work.MotAS.AmatAS2` is homogeneous of degree `1` in the base point `c`.
Consequently the ruling vectors of `{sAS2 = 0}` are **polynomial** in the chart
`c = (X₀, X₁, X₂, 1, 0)` of the residual curve — unlike in the chart `c = (1,X₀,X₁,X₂,0)` used by
`Work.MotAS.ZIAS`, where the pivot `c₃` appears in the denominators (see
`ASRULINGMAIN_AGENT_STATE.md` §"The obstruction").

This file defines

* `asBaseVec3 = (X 0, X 1, X 2, 1, 0)` — the base point of the chart `{c₃ = 1, c₄ = 0}`;
* `ZIAS3 a b g` — the ideal of the residual curve in that chart, i.e. the span of the five cubics
  `kleinRAS a b g (asBaseVec3 K)`;
* `ASrulV3`, `ASrulW3` — the two ruling vectors, normalised by `(x₃,x₄) = (1,0)` resp. `(0,1)`,
  with the constants `(a+2b)(2a-b)` (resp. `(a+2b)²(2a-b)`) cleared (these are non-zero whenever
  `a² - a b - b² ≠ 0`).

The membership statements (`AmatAS2 ⋯ *ᵥ ASrulV3 ∈ radical (ZIAS3 a b g)`) are the AS analogue of
`Work.MotK.TwCensus.AmatP_ker_iff`'s input and are stated in the sibling files
`Submission/Work/MotAS/ASrulV3_mem.lean`, `Submission/Work/MotAS/ASrulW3_mem.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K]

/-- The base point `(X₀,X₁,X₂,1,0)` of the chart `{c₃ = 1, c₄ = 0}` of the residual curve. -/
noncomputable def asBaseVec3 (K : Type*) [CommRing K] : Fin 5 → MvPolynomial (Fin 3) K :=
  ![X 0, X 1, X 2, 1, 0]

@[simp] theorem asBaseVec3_zero {K : Type*} [CommRing K] : asBaseVec3 K 0 = X 0 := rfl
@[simp] theorem asBaseVec3_one {K : Type*} [CommRing K] : asBaseVec3 K 1 = X 1 := rfl
@[simp] theorem asBaseVec3_two {K : Type*} [CommRing K] : asBaseVec3 K 2 = X 2 := rfl
@[simp] theorem asBaseVec3_three {K : Type*} [CommRing K] : asBaseVec3 K 3 = 1 := rfl
@[simp] theorem asBaseVec3_four {K : Type*} [CommRing K] : asBaseVec3 K 4 = 0 := rfl

/-- The ideal of the residual curve `C'` in the chart `{c₃ = 1, c₄ = 0}`. -/
noncomputable def ZIAS3 (a b g : K) : Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span (Set.range (fun k : Fin 5 =>
    kleinRAS (C a) (C b) (C g) (asBaseVec3 K) k))

/-- **The first ruling vector in the chart `{c₃ = 1, c₄ = 0}`**, constants cleared:
it has `(x₃,x₄) = ((a+2b)(2a-b), 0)`. -/
noncomputable def ASrulV3 (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![-C (a + 2 * b) * (C a * X 0 + C (2 * b) * X 0 - C (2 * a) * X 1 * X 2 + C b * X 1 * X 2
        + C a * X 2 - C (2 * b) * X 2),
    C (2 * a - b) * (C (2 * a) * X 2 ^ 2 - C b * X 2 ^ 2 + C a - C (2 * b)),
    C (2 * a - b) * C (a + 2 * b) * X 2,
    C (2 * a - b) * C (a + 2 * b),
    0]

/-- **The second ruling vector in the chart `{c₃ = 1, c₄ = 0}`**, constants cleared:
it has `(x₃,x₄) = (0, (a+2b)²(2a-b))`. -/
noncomputable def ASrulW3 (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![-C (a + 2 * b) * (C (4 * a ^ 2) * X 1 ^ 2 - C (4 * a * b) * X 1 ^ 2 + C (b ^ 2) * X 1 ^ 2
        + C (4 * a ^ 2) * X 1 + C (10 * a * b) * X 1 - C (b ^ 2) * X 1
        - C (3 * a ^ 2) - C (a * b) - C (2 * b ^ 2)),
    -C (2 * a - b) * (C (2 * a ^ 2) * X 0 + C (3 * a * b) * X 0 - C (2 * b ^ 2) * X 0
        + C (4 * a ^ 2) * X 1 * X 2 - C (4 * a * b) * X 1 * X 2 + C (b ^ 2) * X 1 * X 2
        + C (6 * a ^ 2) * X 2 + C (5 * a * b) * X 2 + C (b ^ 2) * X 2),
    -C (a + 2 * b) * C (2 * a - b) * (C (2 * a) * X 1 - C b * X 1 + C (2 * a) + C b),
    0,
    C (a + 2 * b) ^ 2 * C (2 * a - b)]

end Work.MotAS
