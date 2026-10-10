import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASResidual

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The explicit ruling vectors of the AS source ruling divisor (auxiliary definitions)

The AS ruling matrix `Work.MotAS.AmatAS2` (`Submission/Work/MotAS/ASRulingMainAux.lean`) has, on the
base curve `V(ZIAS) ∩ {z₀ = 1, z₄ = 0}`, rank `3`; its kernel — the ruling line of the source
divisor `{sAS2 = 0}` — is spanned by the two vectors below.  They were obtained by solving the
first three row equations of `AmatAS2 a b g ![1,p,q,r,0]` for `(x₀,x₁,x₂)` in terms of the free
coordinates `(x₃,x₄)`, normalised by `(x₃,x₄) = (1,0)` resp. `(0,1)`, and clearing the common
denominator (`p,q,r` are the coordinates `X 0, X 1, X 2` of the base point `c/c₀`).  The two
cleared vectors have `(v₃,v₄) = (δ_V,0)` and `(w₃,w₄) = (0,δ_W)` with
`δ_V = r²(2a-b)(a+2b)` and `δ_W = r²(a+2b)²(2a-b)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K]

/-- **The first AS ruling vector** (denominators cleared by `r²(2a-b)(a+2b)`). -/
noncomputable def ASrulV (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![C (a + 2 * b) * (C (2 * a) * X 0 * X 1 - C a * X 1 * X 2 - C a * X 2 - C b * X 0 * X 1
        + C (2 * b) * X 1 * X 2 - C (2 * b) * X 2),
    C (2 * a - b) * (C (2 * a) * X 1 ^ 2 + C a * X 2 ^ 2 - C b * X 1 ^ 2 - C (2 * b) * X 2 ^ 2),
    C (2 * a - b) * C (a + 2 * b) * (X 1 * X 2),
    C (2 * a - b) * C (a + 2 * b) * X 2 ^ 2,
    0]

/-- **The second AS ruling vector** (denominators cleared by `r²(a+2b)²(2a-b)`). -/
noncomputable def ASrulW (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![-C (a + 2 * b) * (C (4 * a ^ 2) * X 0 ^ 2 + C (4 * a ^ 2) * X 0 * X 2 - C (3 * a ^ 2) * X 2 ^ 2
        - C (4 * a * b) * X 0 ^ 2 + C (10 * a * b) * X 0 * X 2 - C (a * b) * X 2 ^ 2
        + C (b ^ 2) * X 0 ^ 2 - C (b ^ 2) * X 0 * X 2 - C (2 * b ^ 2) * X 2 ^ 2),
    -C (2 * a - b) * (C (4 * a ^ 2) * X 0 * X 1 + C (6 * a ^ 2) * X 1 * X 2 + C (2 * a ^ 2) * X 2
        - C (4 * a * b) * X 0 * X 1 + C (5 * a * b) * X 1 * X 2 + C (3 * a * b) * X 2
        + C (b ^ 2) * X 0 * X 1 + C (b ^ 2) * X 1 * X 2 - C (2 * b ^ 2) * X 2),
    -C (a + 2 * b) * C (2 * a - b) * X 2 * (C (2 * a) * X 0 + C (2 * a) * X 2 - C b * X 0 + C b * X 2),
    0,
    C (a + 2 * b) ^ 2 * C (2 * a - b) * X 2 ^ 2]

/-- The base chart vector `(1,X₀,X₁,X₂,0)`. -/
noncomputable def asBaseVec (K : Type*) [CommRing K] : Fin 5 → MvPolynomial (Fin 3) K :=
  ![1, X 0, X 1, X 2, 0]

@[simp] theorem asBaseVec_zero {K : Type*} [CommRing K] : asBaseVec K 0 = 1 := rfl
@[simp] theorem asBaseVec_one {K : Type*} [CommRing K] : asBaseVec K 1 = X 0 := rfl
@[simp] theorem asBaseVec_two {K : Type*} [CommRing K] : asBaseVec K 2 = X 1 := rfl
@[simp] theorem asBaseVec_three {K : Type*} [CommRing K] : asBaseVec K 3 = X 2 := rfl
@[simp] theorem asBaseVec_four {K : Type*} [CommRing K] : asBaseVec K 4 = 0 := rfl

end Work.MotAS
