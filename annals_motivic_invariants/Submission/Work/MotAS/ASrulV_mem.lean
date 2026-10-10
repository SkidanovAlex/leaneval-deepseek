/-
# `Work.MotAS.ASrulV_mem` — the AS ruling vector lies in the ruling kernel modulo the base curve

For `K` a field of characteristic `5` and parameters `a b g : K`, the fourth component of
`AmatAS2 (C a) (C b) (C g) (asBaseVec K) *ᵥ ASrulV a b g` — the only nonzero component; the other
four vanish identically — squares into the ideal `ZIAS a b g` of the AS residual curve.  Hence the
fifth component lies in `Ideal.radical (ZIAS a b g)`, which is the statement needed for the ruling
of the AS source divisor.

The certificate is the explicit identity

  `asRulV_R4 ^ 2 = Σ_{i=1..4} asRulV_Qi * zcubAS i`  (in characteristic `5`),

recorded in the form of the integral identity
`asRulV_R4 ^ 2 - Σ asRulV_Qi * zcubAS i = 5 * asRulV_Z`, whence it follows after `5 = 0`.
-/
import Mathlib
import Submission.Work.MotAS.ASRulingVec
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASResidual
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial

/-- The fourth (and only nonzero) component of `AmatAS2 a b g (asBaseVec K) *ᵥ ASrulV a b g`:
the contraction of the last row of the AS ruling matrix with the first AS ruling vector. -/
private noncomputable def asRulV_R4 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  4 * C a^(3:ℕ) * C g * (X 2)^(3:ℕ) + 4 * C a^(2:ℕ) * C b * C g * (X 2)^(3:ℕ) - 7 * C a * C b^(2:ℕ) * C g * (X 2)^(3:ℕ) + 2 * C b^(3:ℕ) * C g * (X 2)^(3:ℕ) + 2 * C a^(3:ℕ) * (X 0)^(2:ℕ) * (X 1) - C a^(3:ℕ) * (X 0) * (X 1) * (X 2) + 8 * C a^(3:ℕ) * (X 1)^(3:ℕ) - 3 * C a^(3:ℕ) * (X 1) * (X 2)^(2:ℕ) + 7 * C a^(2:ℕ) * C b * (X 0)^(2:ℕ) * (X 1) - 2 * C a^(2:ℕ) * C b * (X 0) * (X 1) * (X 2) - 4 * C a^(2:ℕ) * C b * (X 1)^(3:ℕ) - 18 * C a^(2:ℕ) * C b * (X 1) * (X 2)^(2:ℕ) + 4 * C a * C b^(2:ℕ) * (X 0)^(2:ℕ) * (X 1) + 4 * C a * C b^(2:ℕ) * (X 0) * (X 1) * (X 2) - 2 * C a * C b^(2:ℕ) * (X 1)^(3:ℕ) + 9 * C a * C b^(2:ℕ) * (X 1) * (X 2)^(2:ℕ) - 4 * C b^(3:ℕ) * (X 0)^(2:ℕ) * (X 1) + 8 * C b^(3:ℕ) * (X 0) * (X 1) * (X 2) + C b^(3:ℕ) * (X 1)^(3:ℕ) + 6 * C b^(3:ℕ) * (X 1) * (X 2)^(2:ℕ) - C a^(3:ℕ) * (X 0) * (X 2) - 8 * C a^(3:ℕ) * (X 1)^(2:ℕ) - 7 * C a^(3:ℕ) * (X 2)^(2:ℕ) - 6 * C a^(2:ℕ) * C b * (X 0) * (X 2) + 12 * C a^(2:ℕ) * C b * (X 1)^(2:ℕ) + 6 * C a^(2:ℕ) * C b * (X 2)^(2:ℕ) - 12 * C a * C b^(2:ℕ) * (X 0) * (X 2) - 6 * C a * C b^(2:ℕ) * (X 1)^(2:ℕ) - 12 * C a * C b^(2:ℕ) * (X 2)^(2:ℕ) - 8 * C b^(3:ℕ) * (X 0) * (X 2) + C b^(3:ℕ) * (X 1)^(2:ℕ) - 4 * C b^(3:ℕ) * (X 2)^(2:ℕ)

/-- Certificate cofactor of `zcubAS a b g 1`. -/
private noncomputable def asRulV_Q1 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  3 * C a^(2:ℕ) * (X 0) * (X 2)^(2:ℕ) + 3 * C a^(2:ℕ) * (X 2)^(3:ℕ) + 2 * C a * C b * (X 0) * (X 2)^(2:ℕ) + 2 * C b^(2:ℕ) * (X 0) * (X 2)^(2:ℕ) + 3 * C b^(2:ℕ) * (X 2)^(3:ℕ)

/-- Certificate cofactor of `zcubAS a b g 2`. -/
private noncomputable def asRulV_Q2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  3 * C a^(2:ℕ) * (X 0) * (X 1) * (X 2) + 2 * C a * C b * (X 0) * (X 1) * (X 2) + 2 * C b^(2:ℕ) * (X 0) * (X 1) * (X 2) + 4 * C a^(2:ℕ) * (X 2)^(2:ℕ) + C a * C b * (X 2)^(2:ℕ) + C b^(2:ℕ) * (X 2)^(2:ℕ)

/-- Certificate cofactor of `zcubAS a b g 3`. -/
private noncomputable def asRulV_Q3 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  C a^(2:ℕ) * (X 0) * (X 1)^(2:ℕ) + 2 * C a^(2:ℕ) * (X 0) * (X 2)^(2:ℕ) + 4 * C a^(2:ℕ) * (X 1)^(2:ℕ) * (X 2) + 2 * C a^(2:ℕ) * (X 2)^(3:ℕ) + 4 * C a * C b * (X 0) * (X 1)^(2:ℕ) + 2 * C a * C b * (X 2)^(3:ℕ) + 4 * C b^(2:ℕ) * (X 0) * (X 1)^(2:ℕ) + 2 * C b^(2:ℕ) * (X 0) * (X 2)^(2:ℕ) + 4 * C b^(2:ℕ) * (X 1)^(2:ℕ) * (X 2) + 3 * C b^(2:ℕ) * (X 2)^(3:ℕ) + C a^(2:ℕ) * (X 1) * (X 2) + 4 * C a * C b * (X 1) * (X 2) + 4 * C b^(2:ℕ) * (X 1) * (X 2)

/-- Certificate cofactor of `zcubAS a b g 4`. -/
private noncomputable def asRulV_Q4 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  4 * C a^(2:ℕ) * C g * (X 2)^(3:ℕ) + C a * C b * C g * (X 2)^(3:ℕ) + C b^(2:ℕ) * C g * (X 2)^(3:ℕ) + 3 * C a^(2:ℕ) * (X 1)^(3:ℕ) + C a * C b * (X 1) * (X 2)^(2:ℕ) + 3 * C b^(2:ℕ) * (X 1)^(3:ℕ) + 3 * C a^(2:ℕ) * (X 0) * (X 2) + 2 * C a^(2:ℕ) * (X 1)^(2:ℕ) + 2 * C a^(2:ℕ) * (X 2)^(2:ℕ) + 2 * C a * C b * (X 0) * (X 2) + 3 * C a * C b * (X 1)^(2:ℕ) + 2 * C b^(2:ℕ) * (X 0) * (X 2) + 3 * C b^(2:ℕ) * (X 1)^(2:ℕ) + 2 * C b^(2:ℕ) * (X 2)^(2:ℕ)

/-- Chunk 0 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z0 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  4 * C a^(6:ℕ) * C g^(2:ℕ) * (X 2)^(6:ℕ) + 5 * C a^(5:ℕ) * C b * C g^(2:ℕ) * (X 2)^(6:ℕ) - 9 * C a^(4:ℕ) * C b^(2:ℕ) * C g^(2:ℕ) * (X 2)^(6:ℕ) - 7 * C a^(3:ℕ) * C b^(3:ℕ) * C g^(2:ℕ) * (X 2)^(6:ℕ) + 14 * C a^(2:ℕ) * C b^(4:ℕ) * C g^(2:ℕ) * (X 2)^(6:ℕ) - 5 * C a * C b^(5:ℕ) * C g^(2:ℕ) * (X 2)^(6:ℕ) + C b^(6:ℕ) * C g^(2:ℕ) * (X 2)^(6:ℕ) + C a^(6:ℕ) * C g * (X 0)^(2:ℕ) * (X 1) * (X 2)^(3:ℕ) - C a^(6:ℕ) * C g * (X 0) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) - C a^(6:ℕ) * C g * (X 0) * (X 1) * (X 2)^(4:ℕ) + 14 * C a^(6:ℕ) * C g * (X 1)^(3:ℕ) * (X 2)^(3:ℕ) - 6 * C a^(6:ℕ) * C g * (X 1) * (X 2)^(5:ℕ) + 11 * C a^(5:ℕ) * C b * C g * (X 0)^(2:ℕ) * (X 1) * (X 2)^(3:ℕ) - 4 * C a^(5:ℕ) * C b * C g * (X 0) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) - 7 * C a^(5:ℕ) * C b * C g * (X 0) * (X 1) * (X 2)^(4:ℕ) + 2 * C a^(5:ℕ) * C b * C g * (X 1)^(3:ℕ) * (X 2)^(3:ℕ) - 37 * C a^(5:ℕ) * C b * C g * (X 1) * (X 2)^(5:ℕ) + 12 * C a^(4:ℕ) * C b^(2:ℕ) * C g * (X 0)^(2:ℕ) * (X 1) * (X 2)^(3:ℕ) - 3 * C a^(4:ℕ) * C b^(2:ℕ) * C g * (X 0) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) + 6 * C a^(4:ℕ) * C b^(2:ℕ) * C g * (X 0) * (X 1) * (X 2)^(4:ℕ) - 32 * C a^(4:ℕ) * C b^(2:ℕ) * C g * (X 1)^(3:ℕ) * (X 2)^(3:ℕ) - 5 * C a^(4:ℕ) * C b^(2:ℕ) * C g * (X 1) * (X 2)^(5:ℕ) - 16 * C a^(3:ℕ) * C b^(3:ℕ) * C g * (X 0)^(2:ℕ) * (X 1) * (X 2)^(3:ℕ) + 2 * C a^(3:ℕ) * C b^(3:ℕ) * C g * (X 0) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) + 23 * C a^(3:ℕ) * C b^(3:ℕ) * C g * (X 0) * (X 1) * (X 2)^(4:ℕ)

/-- Chunk 1 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z1 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  14 * C a^(3:ℕ) * C b^(3:ℕ) * C g * (X 1)^(3:ℕ) * (X 2)^(3:ℕ) + 71 * C a^(3:ℕ) * C b^(3:ℕ) * C g * (X 1) * (X 2)^(5:ℕ) - 12 * C a^(2:ℕ) * C b^(4:ℕ) * C g * (X 0)^(2:ℕ) * (X 1) * (X 2)^(3:ℕ) + 3 * C a^(2:ℕ) * C b^(4:ℕ) * C g * (X 0) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) - C a^(2:ℕ) * C b^(4:ℕ) * C g * (X 0) * (X 1) * (X 2)^(4:ℕ) + 2 * C a^(2:ℕ) * C b^(4:ℕ) * C g * (X 1)^(3:ℕ) * (X 2)^(3:ℕ) - 31 * C a^(2:ℕ) * C b^(4:ℕ) * C g * (X 1) * (X 2)^(5:ℕ) + 15 * C a * C b^(5:ℕ) * C g * (X 0)^(2:ℕ) * (X 1) * (X 2)^(3:ℕ) - 18 * C a * C b^(5:ℕ) * C g * (X 0) * (X 1) * (X 2)^(4:ℕ) - 2 * C a * C b^(5:ℕ) * C g * (X 1)^(3:ℕ) * (X 2)^(3:ℕ) - 11 * C a * C b^(5:ℕ) * C g * (X 1) * (X 2)^(5:ℕ) - 4 * C b^(6:ℕ) * C g * (X 0)^(2:ℕ) * (X 1) * (X 2)^(3:ℕ) - 2 * C b^(6:ℕ) * C g * (X 0) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) + 6 * C b^(6:ℕ) * C g * (X 0) * (X 1) * (X 2)^(4:ℕ) + 2 * C b^(6:ℕ) * C g * (X 1) * (X 2)^(5:ℕ) - 3 * C a^(6:ℕ) * C g * (X 0) * (X 2)^(4:ℕ) - 16 * C a^(6:ℕ) * C g * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) - 12 * C a^(6:ℕ) * C g * (X 2)^(5:ℕ) + C a^(6:ℕ) * (X 0)^(4:ℕ) * (X 1)^(2:ℕ) + C a^(6:ℕ) * (X 0)^(4:ℕ) * (X 2)^(2:ℕ) - C a^(6:ℕ) * (X 0)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2) + 2 * C a^(6:ℕ) * (X 0)^(3:ℕ) * (X 2)^(3:ℕ) + 5 * C a^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)^(4:ℕ) - 2 * C a^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) - 2 * C a^(6:ℕ) * (X 0) * (X 1)^(4:ℕ) * (X 2)

/-- Chunk 2 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  - C a^(6:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) - 2 * C a^(6:ℕ) * (X 0) * (X 2)^(5:ℕ) + 14 * C a^(6:ℕ) * (X 1)^(6:ℕ) - 10 * C a^(6:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ) + 2 * C a^(6:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ) - C a^(6:ℕ) * (X 2)^(6:ℕ) - 16 * C a^(5:ℕ) * C b * C g * (X 0) * (X 2)^(4:ℕ) + 2 * C a^(5:ℕ) * C b * C g * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) - 3 * C a^(5:ℕ) * C b * C g * (X 2)^(5:ℕ) + 6 * C a^(5:ℕ) * C b * (X 0)^(4:ℕ) * (X 1)^(2:ℕ) - C a^(5:ℕ) * C b * (X 0)^(4:ℕ) * (X 2)^(2:ℕ) - 5 * C a^(5:ℕ) * C b * (X 0)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2) - C a^(5:ℕ) * C b * (X 0)^(3:ℕ) * (X 2)^(3:ℕ) + 18 * C a^(5:ℕ) * C b * (X 0)^(2:ℕ) * (X 1)^(4:ℕ) - 24 * C a^(5:ℕ) * C b * (X 0)^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) - 3 * C a^(5:ℕ) * C b * (X 0) * (X 1)^(4:ℕ) * (X 2) + 8 * C a^(5:ℕ) * C b * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) + C a^(5:ℕ) * C b * (X 0) * (X 2)^(5:ℕ) - 14 * C a^(5:ℕ) * C b * (X 1)^(6:ℕ) - 53 * C a^(5:ℕ) * C b * (X 1)^(4:ℕ) * (X 2)^(2:ℕ) + 22 * C a^(5:ℕ) * C b * (X 1)^(2:ℕ) * (X 2)^(4:ℕ) + C a^(5:ℕ) * C b * (X 2)^(6:ℕ) - 27 * C a^(4:ℕ) * C b^(2:ℕ) * C g * (X 0) * (X 2)^(4:ℕ) + 31 * C a^(4:ℕ) * C b^(2:ℕ) * C g * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) + 10 * C a^(4:ℕ) * C b^(2:ℕ) * C g * (X 2)^(5:ℕ)

/-- Chunk 3 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z3 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  12 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0)^(4:ℕ) * (X 1)^(2:ℕ) - 4 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2) + 2 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0)^(3:ℕ) * (X 2)^(3:ℕ) - 48 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) + 2 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ) + 18 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0) * (X 1)^(4:ℕ) * (X 2) + 7 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) - C a^(4:ℕ) * C b^(2:ℕ) * (X 0) * (X 2)^(5:ℕ) - 2 * C a^(4:ℕ) * C b^(2:ℕ) * (X 1)^(6:ℕ) + 62 * C a^(4:ℕ) * C b^(2:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ) + 55 * C a^(4:ℕ) * C b^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ) - C a^(4:ℕ) * C b^(2:ℕ) * (X 2)^(6:ℕ) - 13 * C a^(3:ℕ) * C b^(3:ℕ) * C g * (X 0) * (X 2)^(4:ℕ) - 46 * C a^(3:ℕ) * C b^(3:ℕ) * C g * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) - 48 * C a^(3:ℕ) * C b^(3:ℕ) * C g * (X 2)^(5:ℕ) + 6 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(4:ℕ) * (X 1)^(2:ℕ) - C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(4:ℕ) * (X 2)^(2:ℕ) + 17 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2) - 2 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(3:ℕ) * (X 2)^(3:ℕ) - 23 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(2:ℕ) * (X 1)^(4:ℕ) + 2 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) - C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ) + 22 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0) * (X 1)^(4:ℕ) * (X 2) - 49 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) + 2 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0) * (X 2)^(5:ℕ)

/-- Chunk 4 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z4 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  4 * C a^(3:ℕ) * C b^(3:ℕ) * (X 1)^(6:ℕ) + 18 * C a^(3:ℕ) * C b^(3:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ) - 70 * C a^(3:ℕ) * C b^(3:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ) + 2 * C a^(3:ℕ) * C b^(3:ℕ) * (X 2)^(6:ℕ) + 17 * C a^(2:ℕ) * C b^(4:ℕ) * C g * (X 0) * (X 2)^(4:ℕ) + 29 * C a^(2:ℕ) * C b^(4:ℕ) * C g * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) + 32 * C a^(2:ℕ) * C b^(4:ℕ) * C g * (X 2)^(5:ℕ) - 7 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(4:ℕ) * (X 1)^(2:ℕ) - C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(4:ℕ) * (X 2)^(2:ℕ) + 33 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2) + C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(3:ℕ) * (X 2)^(3:ℕ) + 7 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(2:ℕ) * (X 1)^(4:ℕ) + 58 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) + 2 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ) - 14 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0) * (X 1)^(4:ℕ) * (X 2) - 44 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) - 2 * C a^(2:ℕ) * C b^(4:ℕ) * (X 1)^(6:ℕ) - 22 * C a^(2:ℕ) * C b^(4:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ) - 25 * C a^(2:ℕ) * C b^(4:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ) + 14 * C a * C b^(5:ℕ) * C g * (X 0) * (X 2)^(4:ℕ) - 7 * C a * C b^(5:ℕ) * C g * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) + 3 * C a * C b^(5:ℕ) * C g * (X 2)^(5:ℕ) - 4 * C a * C b^(5:ℕ) * (X 0)^(4:ℕ) * (X 1)^(2:ℕ) + 8 * C a * C b^(5:ℕ) * (X 0)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2) + C a * C b^(5:ℕ) * (X 0)^(3:ℕ) * (X 2)^(3:ℕ)

/-- Chunk 5 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z5 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  7 * C a * C b^(5:ℕ) * (X 0)^(2:ℕ) * (X 1)^(4:ℕ) + 6 * C a * C b^(5:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) - C a * C b^(5:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ) - 3 * C a * C b^(5:ℕ) * (X 0) * (X 1)^(4:ℕ) * (X 2) + 39 * C a * C b^(5:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) - C a * C b^(5:ℕ) * (X 0) * (X 2)^(5:ℕ) - 2 * C a * C b^(5:ℕ) * (X 1)^(6:ℕ) - C a * C b^(5:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ) + 22 * C a * C b^(5:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ) + C a * C b^(5:ℕ) * (X 2)^(6:ℕ) - 7 * C b^(6:ℕ) * C g * (X 0) * (X 2)^(4:ℕ) - C b^(6:ℕ) * C g * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) - 4 * C b^(6:ℕ) * C g * (X 2)^(5:ℕ) + 4 * C b^(6:ℕ) * (X 0)^(4:ℕ) * (X 1)^(2:ℕ) - 12 * C b^(6:ℕ) * (X 0)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2) - 2 * C b^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)^(4:ℕ) + 2 * C b^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) + 5 * C b^(6:ℕ) * (X 0) * (X 1)^(4:ℕ) * (X 2) + 20 * C b^(6:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ) - C b^(6:ℕ) * (X 1)^(6:ℕ) + 2 * C b^(6:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ) + 8 * C b^(6:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ) - 3 * C a^(6:ℕ) * (X 0)^(3:ℕ) * (X 1) * (X 2) - 7 * C a^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)^(3:ℕ) - 7 * C a^(6:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)

/-- Chunk 6 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z6 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  3 * C a^(6:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2) + 4 * C a^(6:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ) - 26 * C a^(6:ℕ) * (X 1)^(5:ℕ) - 9 * C a^(6:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) + 5 * C a^(6:ℕ) * (X 1) * (X 2)^(4:ℕ) - 10 * C a^(5:ℕ) * C b * (X 0)^(3:ℕ) * (X 1) * (X 2) - 14 * C a^(5:ℕ) * C b * (X 0)^(2:ℕ) * (X 1)^(3:ℕ) - 11 * C a^(5:ℕ) * C b * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ) - 19 * C a^(5:ℕ) * C b * (X 0) * (X 1)^(3:ℕ) * (X 2) + 14 * C a^(5:ℕ) * C b * (X 0) * (X 1) * (X 2)^(3:ℕ) + 51 * C a^(5:ℕ) * C b * (X 1)^(5:ℕ) + 70 * C a^(5:ℕ) * C b * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) + 42 * C a^(5:ℕ) * C b * (X 1) * (X 2)^(4:ℕ) - 29 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0)^(3:ℕ) * (X 1) * (X 2) + 14 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0)^(2:ℕ) * (X 1)^(3:ℕ) + 4 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ) - 48 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2) + 43 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ) - 32 * C a^(4:ℕ) * C b^(2:ℕ) * (X 1)^(5:ℕ) - 148 * C a^(4:ℕ) * C b^(2:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) - 56 * C a^(4:ℕ) * C b^(2:ℕ) * (X 1) * (X 2)^(4:ℕ) - 48 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(3:ℕ) * (X 1) * (X 2) + 15 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(2:ℕ) * (X 1)^(3:ℕ) - 15 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ) - 7 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2)

/-- Chunk 7 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z7 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  72 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ) - 2 * C a^(3:ℕ) * C b^(3:ℕ) * (X 1)^(5:ℕ) + 62 * C a^(3:ℕ) * C b^(3:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) + 95 * C a^(3:ℕ) * C b^(3:ℕ) * (X 1) * (X 2)^(4:ℕ) - 31 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(3:ℕ) * (X 1) * (X 2) - 24 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(2:ℕ) * (X 1)^(3:ℕ) - 71 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ) + 45 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2) + 4 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ) + 6 * C a^(2:ℕ) * C b^(4:ℕ) * (X 1)^(5:ℕ) + 20 * C a^(2:ℕ) * C b^(4:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) + 8 * C a * C b^(5:ℕ) * (X 0)^(3:ℕ) * (X 1) * (X 2) + 13 * C a * C b^(5:ℕ) * (X 0)^(2:ℕ) * (X 1)^(3:ℕ) - 38 * C a * C b^(5:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ) - 16 * C a * C b^(5:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2) - 104 * C a * C b^(5:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ) - 5 * C a * C b^(5:ℕ) * (X 1)^(5:ℕ) - 15 * C a * C b^(5:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ) - 43 * C a * C b^(5:ℕ) * (X 1) * (X 2)^(4:ℕ) + 12 * C b^(6:ℕ) * (X 0)^(3:ℕ) * (X 1) * (X 2) - 2 * C b^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)^(3:ℕ) - 20 * C b^(6:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ) - 34 * C b^(6:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ) - 2 * C b^(6:ℕ) * (X 1)^(5:ℕ) - 2 * C b^(6:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ)

/-- Chunk 8 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z8 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  - 11 * C b^(6:ℕ) * (X 1) * (X 2)^(4:ℕ) - 2 * C a^(6:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ) + C a^(6:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2) + C a^(6:ℕ) * (X 0) * (X 2)^(3:ℕ) + 12 * C a^(6:ℕ) * (X 1)^(4:ℕ) + 21 * C a^(6:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) + 10 * C a^(6:ℕ) * (X 2)^(4:ℕ) - C a^(5:ℕ) * C b * (X 0)^(2:ℕ) * (X 2)^(2:ℕ) + 10 * C a^(5:ℕ) * C b * (X 0) * (X 1)^(2:ℕ) * (X 2) + 13 * C a^(5:ℕ) * C b * (X 0) * (X 2)^(3:ℕ) - 40 * C a^(5:ℕ) * C b * (X 1)^(4:ℕ) - 53 * C a^(5:ℕ) * C b * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) - 18 * C a^(5:ℕ) * C b * (X 2)^(4:ℕ) + 12 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ) + 8 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2) + 24 * C a^(4:ℕ) * C b^(2:ℕ) * (X 0) * (X 2)^(3:ℕ) + 47 * C a^(4:ℕ) * C b^(2:ℕ) * (X 1)^(4:ℕ) + 84 * C a^(4:ℕ) * C b^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) + 42 * C a^(4:ℕ) * C b^(2:ℕ) * (X 2)^(4:ℕ) + 34 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ) - 18 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2) + 24 * C a^(3:ℕ) * C b^(3:ℕ) * (X 0) * (X 2)^(3:ℕ) - 31 * C a^(3:ℕ) * C b^(3:ℕ) * (X 1)^(4:ℕ) - 65 * C a^(3:ℕ) * C b^(3:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) - 17 * C a^(3:ℕ) * C b^(3:ℕ) * (X 2)^(4:ℕ)

/-- Chunk 9 of the correction term `asRulV_Z`. -/
private noncomputable def asRulV_Z9 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  48 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ) - 8 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2) + 48 * C a^(2:ℕ) * C b^(4:ℕ) * (X 0) * (X 2)^(3:ℕ) + 13 * C a^(2:ℕ) * C b^(4:ℕ) * (X 1)^(4:ℕ) + 9 * C a^(2:ℕ) * C b^(4:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) + 21 * C a^(2:ℕ) * C b^(4:ℕ) * (X 2)^(4:ℕ) + 39 * C a * C b^(5:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ) + 17 * C a * C b^(5:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2) + 59 * C a * C b^(5:ℕ) * (X 0) * (X 2)^(3:ℕ) - 3 * C a * C b^(5:ℕ) * (X 1)^(4:ℕ) + 2 * C a * C b^(5:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) + 19 * C a * C b^(5:ℕ) * (X 2)^(4:ℕ) + 12 * C b^(6:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ) - 5 * C b^(6:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2) + 11 * C b^(6:ℕ) * (X 0) * (X 2)^(3:ℕ) - C b^(6:ℕ) * (X 1)^(4:ℕ) - 6 * C b^(6:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ) + 2 * C b^(6:ℕ) * (X 2)^(4:ℕ) - 2 * C a^(6:ℕ) * (X 1) * (X 2)^(2:ℕ) - 3 * C a^(5:ℕ) * C b * (X 1) * (X 2)^(2:ℕ) - C a^(4:ℕ) * C b^(2:ℕ) * (X 1) * (X 2)^(2:ℕ) + 2 * C a^(3:ℕ) * C b^(3:ℕ) * (X 1) * (X 2)^(2:ℕ) + C a^(2:ℕ) * C b^(4:ℕ) * (X 1) * (X 2)^(2:ℕ) - C a * C b^(5:ℕ) * (X 1) * (X 2)^(2:ℕ) - 2 * C b^(6:ℕ) * (X 1) * (X 2)^(2:ℕ)


/-- The correction term: `asRulV_R4 ^ 2 - Σ asRulV_Qi * zcubAS i = 5 * asRulV_Z`.  (Split into
chunks above so that each piece elaborates quickly.) -/
private noncomputable def asRulV_Z {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  asRulV_Z0 a b g + asRulV_Z1 a b g + asRulV_Z2 a b g + asRulV_Z3 a b g + asRulV_Z4 a b g + asRulV_Z5 a b g + asRulV_Z6 a b g + asRulV_Z7 a b g + asRulV_Z8 a b g + asRulV_Z9 a b g


/-- **The AS ruling vector lies in the ruling kernel modulo the AS residual curve.**  The first
four components of `AmatAS2 ⋯ (asBaseVec K) *ᵥ ASrulV a b g` vanish identically and the fifth one
is `asRulV_R4 a b g`, whose square lies in `ZIAS a b g` by the certificate above. -/
theorem ASrulV_mem (K : Type) [Field K] [CharP K 5] (a b g : K) (i : Fin 5) :
    Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (Work.MotAS.asBaseVec K)) (Work.MotAS.ASrulV a b g) i
      ∈ Ideal.radical (Work.MotAS.ZIAS a b g) := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
  have hz1 : zcubAS a b g 1 ∈ ZIAS a b g := by rw [ZIAS]; exact Ideal.subset_span ⟨1, rfl⟩
  have hz2 : zcubAS a b g 2 ∈ ZIAS a b g := by rw [ZIAS]; exact Ideal.subset_span ⟨2, rfl⟩
  have hz3 : zcubAS a b g 3 ∈ ZIAS a b g := by rw [ZIAS]; exact Ideal.subset_span ⟨3, rfl⟩
  have hz4 : zcubAS a b g 4 ∈ ZIAS a b g := by rw [ZIAS]; exact Ideal.subset_span ⟨4, rfl⟩
  have hD : asRulV_R4 a b g ^(2:ℕ)
      - (asRulV_Q1 a b g * zcubAS a b g 1 + asRulV_Q2 a b g * zcubAS a b g 2
        + asRulV_Q3 a b g * zcubAS a b g 3 + asRulV_Q4 a b g * zcubAS a b g 4)
      = 5 * asRulV_Z a b g := by
    simp only [asRulV_R4, asRulV_Q1, asRulV_Q2, asRulV_Q3, asRulV_Q4, asRulV_Z, asRulV_Z0, asRulV_Z1, asRulV_Z2, asRulV_Z3, asRulV_Z4, asRulV_Z5, asRulV_Z6, asRulV_Z7, asRulV_Z8, asRulV_Z9,
        zcubAS, kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
    refl_ring1
  have hsq : asRulV_R4 a b g ^(2:ℕ) ∈ ZIAS a b g := by
    have hdecomp : asRulV_R4 a b g ^(2:ℕ)
        = asRulV_Q1 a b g * zcubAS a b g 1 + asRulV_Q2 a b g * zcubAS a b g 2
          + asRulV_Q3 a b g * zcubAS a b g 3 + asRulV_Q4 a b g * zcubAS a b g 4 := by
      rw [← sub_eq_zero, hD, h5, zero_mul]
    rw [hdecomp]
    exact Ideal.add_mem _
      (Ideal.add_mem _
        (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hz1) (Ideal.mul_mem_left _ _ hz2))
        (Ideal.mul_mem_left _ _ hz3))
      (Ideal.mul_mem_left _ _ hz4)
  have h0 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec K)) (ASrulV a b g)
      (0 : Fin 5) = 0 := by
    simp only [AmatAS2, ASrulV, asBaseVec, asRulV_R4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        map_zero]
    refl_ring1
  have h1 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec K)) (ASrulV a b g)
      (1 : Fin 5) = 0 := by
    simp only [AmatAS2, ASrulV, asBaseVec, asRulV_R4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        map_zero]
    refl_ring1
  have h2 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec K)) (ASrulV a b g)
      (2 : Fin 5) = 0 := by
    simp only [AmatAS2, ASrulV, asBaseVec, asRulV_R4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        map_zero]
    refl_ring1
  have h3 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec K)) (ASrulV a b g)
      (3 : Fin 5) = 0 := by
    simp only [AmatAS2, ASrulV, asBaseVec, asRulV_R4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        map_zero]
    refl_ring1
  have h4 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec K)) (ASrulV a b g)
      (4 : Fin 5) = asRulV_R4 a b g := by
    simp only [AmatAS2, ASrulV, asBaseVec, asRulV_R4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        map_zero]
    refl_ring1
  have hdisj : i = (0 : Fin 5) ∨ i = (1 : Fin 5) ∨ i = (2 : Fin 5) ∨ i = (3 : Fin 5)
      ∨ i = (4 : Fin 5) := by
    fin_cases i <;> simp
  rcases hdisj with h | h | h | h | h <;> rw [h]
  · rw [h0]; exact Ideal.zero_mem _
  · rw [h1]; exact Ideal.zero_mem _
  · rw [h2]; exact Ideal.zero_mem _
  · rw [h3]; exact Ideal.zero_mem _
  · rw [h4]; exact Ideal.mem_radical_iff.mpr ⟨2, hsq⟩

end Work.MotAS
