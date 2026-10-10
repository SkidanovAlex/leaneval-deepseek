/-
# `Work.MotAS.ASrulV3_mem` — the AS ruling vector lies in the ruling kernel modulo the base curve
(in the chart `{c₃ = 1, c₄ = 0}`)

For `K` a field of characteristic `5` and parameters `a b g : K`, the fourth component of
`AmatAS2 (C a) (C b) (C g) (asBaseVec3 K) *ᵥ ASrulV3 a b g` — the only nonzero component; the other
four vanish identically — squares into the ideal `ZIAS3 a b g` of the AS residual curve in the chart
`{c₃ = 1, c₄ = 0}`.  Hence that component lies in `Ideal.radical (ZIAS3 a b g)`.

This is the chart-`3` companion of `Submission/Work/MotAS/ASrulV_mem.lean` (chart `{c₀ = 1}`): the
two charts of the residual curve are related by the substitution `tᵢ = u_{i+1}/u₀` (`z = (1,t)`
versus `z = (u,1)`), under which the chart-`0` certificate *homogenises*.  Concretely, writing
`t = (X₁/X₀, X₂/X₀, 1/X₀)` one has `ASrulV3 = X₀² · ASrulV(t)` and `R4^{(3)} = X₀³ · R4^{(0)}(t)`,
so homogenising the chart-`0` identity `R4^{(0)}² = Σ Qᵢ zcubᵢ + 5 Z` gives the certificate

  `asRulV3_R4 ^ 2 = asRulV3_Q1 * g1 + asRulV3_Q2 * g2 + asRulV3_Q3 * g3 + asRulV3_Q4 * g4`
  (modulo `5`),

with `gᵢ = kleinRAS (C a) (C b) (C g) (asBaseVec3 K) i` the five generators of `ZIAS3`.  The
integral identity `asRulV3_R4 ^ 2 - Σᵢ asRulV3_Qi * gᵢ = 5 * asRulV3_Z` recorded below is the
explicit certificate (it holds over `ℤ[a,b,g,X₀,X₁,X₂]`, hence in every commutative ring).
-/
import Mathlib
import Submission.Work.MotAS.ASRulingVec3
import Submission.Work.MotAS.ASResidual
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial

/-- asRulV3_R4 -/
private noncomputable def asRulV3_R4 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  1 * (C b)^(3:ℕ) * (X 2)^(3:ℕ)
  - 2 * (C a) * (C b)^(2:ℕ) * (X 2)^(3:ℕ)
  - 4 * (C a)^(2:ℕ) * (C b) * (X 2)^(3:ℕ)
  + 8 * (C a)^(3:ℕ) * (X 2)^(3:ℕ)
  - 4 * (C b)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2)
  + 4 * (C a) * (C b)^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)
  + 7 * (C a)^(2:ℕ) * (C b) * (X 1)^(2:ℕ) * (X 2)
  + 2 * (C a)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2)
  + 1 * (C b)^(3:ℕ) * (X 0) * (X 2)^(2:ℕ)
  - 6 * (C a) * (C b)^(2:ℕ) * (X 0) * (X 2)^(2:ℕ)
  + 12 * (C a)^(2:ℕ) * (C b) * (X 0) * (X 2)^(2:ℕ)
  - 8 * (C a)^(3:ℕ) * (X 0) * (X 2)^(2:ℕ)
  + 8 * (C b)^(3:ℕ) * (X 1) * (X 2)
  + 4 * (C a) * (C b)^(2:ℕ) * (X 1) * (X 2)
  - 2 * (C a)^(2:ℕ) * (C b) * (X 1) * (X 2)
  - 1 * (C a)^(3:ℕ) * (X 1) * (X 2)
  - 8 * (C b)^(3:ℕ) * (X 0) * (X 1)
  - 12 * (C a) * (C b)^(2:ℕ) * (X 0) * (X 1)
  - 6 * (C a)^(2:ℕ) * (C b) * (X 0) * (X 1)
  - 1 * (C a)^(3:ℕ) * (X 0) * (X 1)
  + 6 * (C b)^(3:ℕ) * (X 2)
  + 9 * (C a) * (C b)^(2:ℕ) * (X 2)
  - 18 * (C a)^(2:ℕ) * (C b) * (X 2)
  - 3 * (C a)^(3:ℕ) * (X 2)
  - 4 * (C b)^(3:ℕ) * (X 0)
  - 12 * (C a) * (C b)^(2:ℕ) * (X 0)
  + 6 * (C a)^(2:ℕ) * (C b) * (X 0)
  - 7 * (C a)^(3:ℕ) * (X 0)
  + 2 * (C b)^(3:ℕ) * (C g)
  - 7 * (C a) * (C b)^(2:ℕ) * (C g)
  + 4 * (C a)^(2:ℕ) * (C b) * (C g)
  + 4 * (C a)^(3:ℕ) * (C g)

/-- asRulV3_Q1 -/
private noncomputable def asRulV3_Q1 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  2 * (C b)^(2:ℕ) * (X 1)
  + 2 * (C a) * (C b) * (X 1)
  + 3 * (C a)^(2:ℕ) * (X 1)
  + 3 * (C b)^(2:ℕ)
  + 3 * (C a)^(2:ℕ)

/-- asRulV3_Q2 -/
private noncomputable def asRulV3_Q2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  2 * (C b)^(2:ℕ) * (X 1) * (X 2)
  + 2 * (C a) * (C b) * (X 1) * (X 2)
  + 3 * (C a)^(2:ℕ) * (X 1) * (X 2)
  + 1 * (C b)^(2:ℕ) * (X 0)
  + 1 * (C a) * (C b) * (X 0)
  + 4 * (C a)^(2:ℕ) * (X 0)

/-- asRulV3_Q3 -/
private noncomputable def asRulV3_Q3 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  4 * (C b)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 4 * (C a) * (C b) * (X 1) * (X 2)^(2:ℕ)
  + 1 * (C a)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 4 * (C b)^(2:ℕ) * (X 2)^(2:ℕ)
  + 4 * (C a)^(2:ℕ) * (X 2)^(2:ℕ)
  + 4 * (C b)^(2:ℕ) * (X 0) * (X 2)
  + 4 * (C a) * (C b) * (X 0) * (X 2)
  + 1 * (C a)^(2:ℕ) * (X 0) * (X 2)
  + 2 * (C b)^(2:ℕ) * (X 1)
  + 2 * (C a)^(2:ℕ) * (X 1)
  + 3 * (C b)^(2:ℕ)
  + 2 * (C a) * (C b)
  + 2 * (C a)^(2:ℕ)

/-- asRulV3_Q4 -/
private noncomputable def asRulV3_Q4 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  3 * (C b)^(2:ℕ) * (X 2)^(3:ℕ)
  + 3 * (C a)^(2:ℕ) * (X 2)^(3:ℕ)
  + 3 * (C b)^(2:ℕ) * (X 0) * (X 2)^(2:ℕ)
  + 3 * (C a) * (C b) * (X 0) * (X 2)^(2:ℕ)
  + 2 * (C a)^(2:ℕ) * (X 0) * (X 2)^(2:ℕ)
  + 2 * (C b)^(2:ℕ) * (X 0) * (X 1)
  + 2 * (C a) * (C b) * (X 0) * (X 1)
  + 3 * (C a)^(2:ℕ) * (X 0) * (X 1)
  + 1 * (C a) * (C b) * (X 2)
  + 2 * (C b)^(2:ℕ) * (X 0)
  + 2 * (C a)^(2:ℕ) * (X 0)
  + 1 * (C b)^(2:ℕ) * (C g)
  + 1 * (C a) * (C b) * (C g)
  + 4 * (C a)^(2:ℕ) * (C g)

/-- chunk 0 of `asRulV3_Z` -/
private noncomputable def asRulV3_Z_0 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  - 1 * (C b)^(6:ℕ) * (X 2)^(6:ℕ)
  - 2 * (C a) * (C b)^(5:ℕ) * (X 2)^(6:ℕ)
  - 2 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 2)^(6:ℕ)
  + 4 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 2)^(6:ℕ)
  - 2 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 2)^(6:ℕ)
  - 14 * (C a)^(5:ℕ) * (C b) * (X 2)^(6:ℕ)
  + 14 * (C a)^(6:ℕ) * (X 2)^(6:ℕ)
  - 2 * (C b)^(6:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ)
  + 7 * (C a) * (C b)^(5:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ)
  + 7 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ)
  - 23 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ)
  + 18 * (C a)^(5:ℕ) * (C b) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ)
  + 5 * (C a)^(6:ℕ) * (X 1)^(2:ℕ) * (X 2)^(4:ℕ)
  + 4 * (C b)^(6:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ)
  - 4 * (C a) * (C b)^(5:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ)
  - 7 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ)
  + 6 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ)
  + 12 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ)
  + 6 * (C a)^(5:ℕ) * (C b) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ)
  + 1 * (C a)^(6:ℕ) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ)
  - 2 * (C b)^(6:ℕ) * (X 0) * (X 2)^(5:ℕ)
  - 5 * (C a) * (C b)^(5:ℕ) * (X 0) * (X 2)^(5:ℕ)
  + 6 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0) * (X 2)^(5:ℕ)
  - 2 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0) * (X 2)^(5:ℕ)
  - 32 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0) * (X 2)^(5:ℕ)
  + 51 * (C a)^(5:ℕ) * (C b) * (X 0) * (X 2)^(5:ℕ)
  - 26 * (C a)^(6:ℕ) * (X 0) * (X 2)^(5:ℕ)
  - 2 * (C b)^(6:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ)
  + 13 * (C a) * (C b)^(5:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ)
  - 24 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ)
  + 15 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ)
  + 14 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ)
  - 14 * (C a)^(5:ℕ) * (C b) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ)
  - 7 * (C a)^(6:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)^(3:ℕ)
  - 1 * (C b)^(6:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ)
  - 3 * (C a) * (C b)^(5:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ)
  + 13 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ)
  - 31 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ)
  + 47 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ)
  - 40 * (C a)^(5:ℕ) * (C b) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ)
  + 12 * (C a)^(6:ℕ) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ)
  + 5 * (C b)^(6:ℕ) * (X 1) * (X 2)^(4:ℕ)
  - 3 * (C a) * (C b)^(5:ℕ) * (X 1) * (X 2)^(4:ℕ)
  - 14 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 1) * (X 2)^(4:ℕ)
  + 22 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1) * (X 2)^(4:ℕ)
  + 18 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 1) * (X 2)^(4:ℕ)
  - 3 * (C a)^(5:ℕ) * (C b) * (X 1) * (X 2)^(4:ℕ)
  - 2 * (C a)^(6:ℕ) * (X 1) * (X 2)^(4:ℕ)
  - 12 * (C b)^(6:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ)
  + 8 * (C a) * (C b)^(5:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ)

/-- chunk 1 of `asRulV3_Z` -/
private noncomputable def asRulV3_Z_1 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  33 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ)
  + 17 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ)
  - 4 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ)
  - 5 * (C a)^(5:ℕ) * (C b) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ)
  - 1 * (C a)^(6:ℕ) * (X 1)^(3:ℕ) * (X 2)^(2:ℕ)
  - 16 * (C a) * (C b)^(5:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ)
  + 45 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ)
  - 7 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ)
  - 48 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ)
  - 19 * (C a)^(5:ℕ) * (C b) * (X 0) * (X 1) * (X 2)^(3:ℕ)
  + 3 * (C a)^(6:ℕ) * (X 0) * (X 1) * (X 2)^(3:ℕ)
  + 12 * (C b)^(6:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2)
  + 8 * (C a) * (C b)^(5:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2)
  - 31 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2)
  - 48 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2)
  - 29 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2)
  - 10 * (C a)^(5:ℕ) * (C b) * (X 0) * (X 1)^(3:ℕ) * (X 2)
  - 3 * (C a)^(6:ℕ) * (X 0) * (X 1)^(3:ℕ) * (X 2)
  - 5 * (C b)^(6:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 17 * (C a) * (C b)^(5:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  - 8 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  - 18 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 8 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 10 * (C a)^(5:ℕ) * (C b) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 1 * (C a)^(6:ℕ) * (X 0)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 2 * (C b)^(6:ℕ) * (X 2)^(4:ℕ)
  - 1 * (C a) * (C b)^(5:ℕ) * (X 2)^(4:ℕ)
  - 22 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 2)^(4:ℕ)
  + 18 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 2)^(4:ℕ)
  + 62 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 2)^(4:ℕ)
  - 53 * (C a)^(5:ℕ) * (C b) * (X 2)^(4:ℕ)
  - 10 * (C a)^(6:ℕ) * (X 2)^(4:ℕ)
  - 2 * (C b)^(6:ℕ) * (C g) * (X 1) * (X 2)^(3:ℕ)
  + 3 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (C g) * (X 1) * (X 2)^(3:ℕ)
  + 2 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (C g) * (X 1) * (X 2)^(3:ℕ)
  - 3 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (C g) * (X 1) * (X 2)^(3:ℕ)
  - 4 * (C a)^(5:ℕ) * (C b) * (C g) * (X 1) * (X 2)^(3:ℕ)
  - 1 * (C a)^(6:ℕ) * (C g) * (X 1) * (X 2)^(3:ℕ)
  + 2 * (C b)^(6:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ)
  + 6 * (C a) * (C b)^(5:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ)
  + 58 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ)
  + 2 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ)
  - 48 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ)
  - 24 * (C a)^(5:ℕ) * (C b) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ)
  - 2 * (C a)^(6:ℕ) * (X 1)^(2:ℕ) * (X 2)^(2:ℕ)
  - 1 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 1)^(4:ℕ)
  - 1 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1)^(4:ℕ)
  - 1 * (C a)^(5:ℕ) * (C b) * (X 1)^(4:ℕ)
  + 1 * (C a)^(6:ℕ) * (X 1)^(4:ℕ)
  - 2 * (C b)^(6:ℕ) * (X 0) * (X 2)^(3:ℕ)

/-- chunk 2 of `asRulV3_Z` -/
private noncomputable def asRulV3_Z_2 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  - 15 * (C a) * (C b)^(5:ℕ) * (X 0) * (X 2)^(3:ℕ)
  + 20 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0) * (X 2)^(3:ℕ)
  + 62 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0) * (X 2)^(3:ℕ)
  - 148 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0) * (X 2)^(3:ℕ)
  + 70 * (C a)^(5:ℕ) * (C b) * (X 0) * (X 2)^(3:ℕ)
  - 9 * (C a)^(6:ℕ) * (X 0) * (X 2)^(3:ℕ)
  - 20 * (C b)^(6:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)
  - 38 * (C a) * (C b)^(5:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)
  - 71 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)
  - 15 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)
  + 4 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)
  - 11 * (C a)^(5:ℕ) * (C b) * (X 0) * (X 1)^(2:ℕ) * (X 2)
  - 7 * (C a)^(6:ℕ) * (X 0) * (X 1)^(2:ℕ) * (X 2)
  - 6 * (C b)^(6:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ)
  + 2 * (C a) * (C b)^(5:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ)
  + 9 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ)
  - 65 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ)
  + 84 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ)
  - 53 * (C a)^(5:ℕ) * (C b) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ)
  + 21 * (C a)^(6:ℕ) * (X 0)^(2:ℕ) * (X 2)^(2:ℕ)
  + 12 * (C b)^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ)
  + 39 * (C a) * (C b)^(5:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ)
  + 48 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ)
  + 34 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ)
  + 12 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ)
  - 1 * (C a)^(5:ℕ) * (C b) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ)
  - 2 * (C a)^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ)
  - 2 * (C b)^(6:ℕ) * (X 0)^(3:ℕ) * (X 2)
  - 1 * (C a) * (C b)^(5:ℕ) * (X 0)^(3:ℕ) * (X 2)
  + 1 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0)^(3:ℕ) * (X 2)
  + 2 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0)^(3:ℕ) * (X 2)
  - 1 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0)^(3:ℕ) * (X 2)
  - 3 * (C a)^(5:ℕ) * (C b) * (X 0)^(3:ℕ) * (X 2)
  - 2 * (C a)^(6:ℕ) * (X 0)^(3:ℕ) * (X 2)
  - 2 * (C a) * (C b)^(5:ℕ) * (C g) * (X 2)^(3:ℕ)
  + 2 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (C g) * (X 2)^(3:ℕ)
  + 14 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (C g) * (X 2)^(3:ℕ)
  - 32 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (C g) * (X 2)^(3:ℕ)
  + 2 * (C a)^(5:ℕ) * (C b) * (C g) * (X 2)^(3:ℕ)
  + 14 * (C a)^(6:ℕ) * (C g) * (X 2)^(3:ℕ)
  + 20 * (C b)^(6:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 39 * (C a) * (C b)^(5:ℕ) * (X 1) * (X 2)^(2:ℕ)
  - 44 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 1) * (X 2)^(2:ℕ)
  - 49 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 7 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 1) * (X 2)^(2:ℕ)
  + 8 * (C a)^(5:ℕ) * (C b) * (X 1) * (X 2)^(2:ℕ)
  - 1 * (C a)^(6:ℕ) * (X 1) * (X 2)^(2:ℕ)
  - 4 * (C b)^(6:ℕ) * (C g) * (X 1)^(2:ℕ) * (X 2)
  + 15 * (C a) * (C b)^(5:ℕ) * (C g) * (X 1)^(2:ℕ) * (X 2)
  - 12 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (C g) * (X 1)^(2:ℕ) * (X 2)

/-- chunk 3 of `asRulV3_Z` -/
private noncomputable def asRulV3_Z_3 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  - 16 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (C g) * (X 1)^(2:ℕ) * (X 2)
  + 12 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (C g) * (X 1)^(2:ℕ) * (X 2)
  + 11 * (C a)^(5:ℕ) * (C b) * (C g) * (X 1)^(2:ℕ) * (X 2)
  + 1 * (C a)^(6:ℕ) * (C g) * (X 1)^(2:ℕ) * (X 2)
  + 1 * (C a) * (C b)^(5:ℕ) * (X 1)^(3:ℕ)
  + 1 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 1)^(3:ℕ)
  - 2 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1)^(3:ℕ)
  + 2 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 1)^(3:ℕ)
  - 1 * (C a)^(5:ℕ) * (C b) * (X 1)^(3:ℕ)
  + 2 * (C a)^(6:ℕ) * (X 1)^(3:ℕ)
  - 1 * (C b)^(6:ℕ) * (C g) * (X 0) * (X 2)^(2:ℕ)
  - 7 * (C a) * (C b)^(5:ℕ) * (C g) * (X 0) * (X 2)^(2:ℕ)
  + 29 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (C g) * (X 0) * (X 2)^(2:ℕ)
  - 46 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (C g) * (X 0) * (X 2)^(2:ℕ)
  + 31 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (C g) * (X 0) * (X 2)^(2:ℕ)
  + 2 * (C a)^(5:ℕ) * (C b) * (C g) * (X 0) * (X 2)^(2:ℕ)
  - 16 * (C a)^(6:ℕ) * (C g) * (X 0) * (X 2)^(2:ℕ)
  - 34 * (C b)^(6:ℕ) * (X 0) * (X 1) * (X 2)
  - 104 * (C a) * (C b)^(5:ℕ) * (X 0) * (X 1) * (X 2)
  + 4 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0) * (X 1) * (X 2)
  + 72 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0) * (X 1) * (X 2)
  + 43 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0) * (X 1) * (X 2)
  + 14 * (C a)^(5:ℕ) * (C b) * (X 0) * (X 1) * (X 2)
  + 4 * (C a)^(6:ℕ) * (X 0) * (X 1) * (X 2)
  + 11 * (C b)^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)
  + 59 * (C a) * (C b)^(5:ℕ) * (X 0)^(2:ℕ) * (X 1)
  + 48 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0)^(2:ℕ) * (X 1)
  + 24 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0)^(2:ℕ) * (X 1)
  + 24 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0)^(2:ℕ) * (X 1)
  + 13 * (C a)^(5:ℕ) * (C b) * (X 0)^(2:ℕ) * (X 1)
  + 1 * (C a)^(6:ℕ) * (X 0)^(2:ℕ) * (X 1)
  + 8 * (C b)^(6:ℕ) * (X 2)^(2:ℕ)
  + 22 * (C a) * (C b)^(5:ℕ) * (X 2)^(2:ℕ)
  - 25 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 2)^(2:ℕ)
  - 70 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 2)^(2:ℕ)
  + 55 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 2)^(2:ℕ)
  + 22 * (C a)^(5:ℕ) * (C b) * (X 2)^(2:ℕ)
  + 2 * (C a)^(6:ℕ) * (X 2)^(2:ℕ)
  + 6 * (C b)^(6:ℕ) * (C g) * (X 1) * (X 2)
  - 18 * (C a) * (C b)^(5:ℕ) * (C g) * (X 1) * (X 2)
  - 1 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (C g) * (X 1) * (X 2)
  + 23 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (C g) * (X 1) * (X 2)
  + 6 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (C g) * (X 1) * (X 2)
  - 7 * (C a)^(5:ℕ) * (C b) * (C g) * (X 1) * (X 2)
  - 1 * (C a)^(6:ℕ) * (C g) * (X 1) * (X 2)
  - 1 * (C a) * (C b)^(5:ℕ) * (X 1)^(2:ℕ)
  + 2 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 1)^(2:ℕ)
  - 1 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1)^(2:ℕ)
  + 2 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 1)^(2:ℕ)
  - 11 * (C b)^(6:ℕ) * (X 0) * (X 2)

/-- chunk 4 of `asRulV3_Z` -/
private noncomputable def asRulV3_Z_4 {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  - 43 * (C a) * (C b)^(5:ℕ) * (X 0) * (X 2)
  + 95 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0) * (X 2)
  - 56 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0) * (X 2)
  + 42 * (C a)^(5:ℕ) * (C b) * (X 0) * (X 2)
  + 5 * (C a)^(6:ℕ) * (X 0) * (X 2)
  - 7 * (C b)^(6:ℕ) * (C g) * (X 0) * (X 1)
  + 14 * (C a) * (C b)^(5:ℕ) * (C g) * (X 0) * (X 1)
  + 17 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (C g) * (X 0) * (X 1)
  - 13 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (C g) * (X 0) * (X 1)
  - 27 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (C g) * (X 0) * (X 1)
  - 16 * (C a)^(5:ℕ) * (C b) * (C g) * (X 0) * (X 1)
  - 3 * (C a)^(6:ℕ) * (C g) * (X 0) * (X 1)
  + 2 * (C b)^(6:ℕ) * (X 0)^(2:ℕ)
  + 19 * (C a) * (C b)^(5:ℕ) * (X 0)^(2:ℕ)
  + 21 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (X 0)^(2:ℕ)
  - 17 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 0)^(2:ℕ)
  + 42 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 0)^(2:ℕ)
  - 18 * (C a)^(5:ℕ) * (C b) * (X 0)^(2:ℕ)
  + 10 * (C a)^(6:ℕ) * (X 0)^(2:ℕ)
  + 2 * (C b)^(6:ℕ) * (C g) * (X 2)
  - 11 * (C a) * (C b)^(5:ℕ) * (C g) * (X 2)
  - 31 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (C g) * (X 2)
  + 71 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (C g) * (X 2)
  - 5 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (C g) * (X 2)
  - 37 * (C a)^(5:ℕ) * (C b) * (C g) * (X 2)
  - 6 * (C a)^(6:ℕ) * (C g) * (X 2)
  - 1 * (C a) * (C b)^(5:ℕ) * (X 1)
  + 2 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (X 1)
  - 1 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (X 1)
  + 1 * (C a)^(5:ℕ) * (C b) * (X 1)
  - 2 * (C a)^(6:ℕ) * (X 1)
  - 4 * (C b)^(6:ℕ) * (C g) * (X 0)
  + 3 * (C a) * (C b)^(5:ℕ) * (C g) * (X 0)
  + 32 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (C g) * (X 0)
  - 48 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (C g) * (X 0)
  + 10 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (C g) * (X 0)
  - 3 * (C a)^(5:ℕ) * (C b) * (C g) * (X 0)
  - 12 * (C a)^(6:ℕ) * (C g) * (X 0)
  + 1 * (C b)^(6:ℕ) * (C g)^(2:ℕ)
  - 5 * (C a) * (C b)^(5:ℕ) * (C g)^(2:ℕ)
  + 14 * (C a)^(2:ℕ) * (C b)^(4:ℕ) * (C g)^(2:ℕ)
  - 7 * (C a)^(3:ℕ) * (C b)^(3:ℕ) * (C g)^(2:ℕ)
  - 9 * (C a)^(4:ℕ) * (C b)^(2:ℕ) * (C g)^(2:ℕ)
  + 5 * (C a)^(5:ℕ) * (C b) * (C g)^(2:ℕ)
  + 4 * (C a)^(6:ℕ) * (C g)^(2:ℕ)
  + 1 * (C a) * (C b)^(5:ℕ)
  + 2 * (C a)^(3:ℕ) * (C b)^(3:ℕ)
  - 1 * (C a)^(4:ℕ) * (C b)^(2:ℕ)
  + 1 * (C a)^(5:ℕ) * (C b)
  - 1 * (C a)^(6:ℕ)

/-- asRulV3_Z, split into chunks above. -/
private noncomputable def asRulV3_Z {K : Type*} [CommRing K] (a b g : K) : MvPolynomial (Fin 3) K :=
  asRulV3_Z_0 a b g + asRulV3_Z_1 a b g + asRulV3_Z_2 a b g + asRulV3_Z_3 a b g + asRulV3_Z_4 a b g

/-- **The AS ruling vector lies in the ruling kernel modulo the AS residual curve** (chart
`{c₃ = 1, c₄ = 0}`).  Components `0,…,3` of `AmatAS2 ⋯ (asBaseVec3 K) *ᵥ ASrulV3 a b g` vanish
identically and component `4` is `asRulV3_R4 a b g`, whose square lies in `ZIAS3 a b g` by the
certificate above. -/
theorem ASrulV3_mem (K : Type) [Field K] [CharP K 5] (a b g : K) (i : Fin 5) :
    Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (Work.MotAS.asBaseVec3 K)) (Work.MotAS.ASrulV3 a b g) i
      ∈ Ideal.radical (Work.MotAS.ZIAS3 a b g) := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
  have hz1 : kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 1 ∈ ZIAS3 a b g := by
    rw [ZIAS3]; exact Ideal.subset_span ⟨1, rfl⟩
  have hz2 : kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 2 ∈ ZIAS3 a b g := by
    rw [ZIAS3]; exact Ideal.subset_span ⟨2, rfl⟩
  have hz3 : kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 3 ∈ ZIAS3 a b g := by
    rw [ZIAS3]; exact Ideal.subset_span ⟨3, rfl⟩
  have hz4 : kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 4 ∈ ZIAS3 a b g := by
    rw [ZIAS3]; exact Ideal.subset_span ⟨4, rfl⟩
  have hD : asRulV3_R4 a b g ^(2:ℕ)
      - (asRulV3_Q1 a b g * kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 1
        + asRulV3_Q2 a b g * kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 2
        + asRulV3_Q3 a b g * kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 3
        + asRulV3_Q4 a b g * kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 4)
      = 5 * asRulV3_Z a b g := by
    simp only [asRulV3_R4, asRulV3_Q1, asRulV3_Q2, asRulV3_Q3, asRulV3_Q4,
      asRulV3_Z, asRulV3_Z_0, asRulV3_Z_1, asRulV3_Z_2, asRulV3_Z_3, asRulV3_Z_4,
      kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
      asBaseVec3, asBaseVec3_zero, asBaseVec3_one, asBaseVec3_two, asBaseVec3_three,
      asBaseVec3_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Matrix.of_apply, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_zero]
    refl_ring1
  have hsq : asRulV3_R4 a b g ^(2:ℕ) ∈ ZIAS3 a b g := by
    have hdecomp : asRulV3_R4 a b g ^(2:ℕ)
        = asRulV3_Q1 a b g * kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 1
          + asRulV3_Q2 a b g * kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 2
          + asRulV3_Q3 a b g * kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 3
          + asRulV3_Q4 a b g * kleinRAS (C a) (C b) (C g) (asBaseVec3 K) 4 := by
      rw [← sub_eq_zero, hD, h5, zero_mul]
    rw [hdecomp]
    exact Ideal.add_mem _
      (Ideal.add_mem _
        (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hz1) (Ideal.mul_mem_left _ _ hz2))
        (Ideal.mul_mem_left _ _ hz3))
      (Ideal.mul_mem_left _ _ hz4)
  have h0 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec3 K)) (ASrulV3 a b g)
      (0 : Fin 5) = 0 := by
    simp only [AmatAS2, ASrulV3, asBaseVec3, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        map_zero]
    refl_ring1
  have h1 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec3 K)) (ASrulV3 a b g)
      (1 : Fin 5) = 0 := by
    simp only [AmatAS2, ASrulV3, asBaseVec3, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        map_zero]
    refl_ring1
  have h2 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec3 K)) (ASrulV3 a b g)
      (2 : Fin 5) = 0 := by
    simp only [AmatAS2, ASrulV3, asBaseVec3, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        map_zero]
    refl_ring1
  have h3 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec3 K)) (ASrulV3 a b g)
      (3 : Fin 5) = 0 := by
    simp only [AmatAS2, ASrulV3, asBaseVec3, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Fin.isValue, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        map_zero]
    refl_ring1
  have h4 : Matrix.mulVec (AmatAS2 (C a) (C b) (C g) (asBaseVec3 K)) (ASrulV3 a b g)
      (4 : Fin 5) = asRulV3_R4 a b g := by
    simp only [AmatAS2, ASrulV3, asBaseVec3, asRulV3_R4, Matrix.mulVec, dotProduct,
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
