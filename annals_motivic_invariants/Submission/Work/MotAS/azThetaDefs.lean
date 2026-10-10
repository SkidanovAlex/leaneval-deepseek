import Mathlib
import Submission.Work.MotAS.CensusAS2

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.azThetaDefs` — the parametrisation data of the AS chart surface `{f̂₀ = 0}`

The forward chart map of the corrected AS (characteristic-`5`, Artin–Schreier) Crauder–Katz chart is
`f = P^AS ∘ Stereo^AS(pAS0, ·)` (`Submission/Work/MotAS/CensusAS2.lean`), whose `0`-th component
`f̂₀ = fwVecAS2 a b g 0` cuts out the preimage of the target line at infinity.  The inverse chart
map `χ = π_{pAS0} ∘ R^AS` restricted to that plane (in the affine chart `ẑ₃ = 1`, coordinates `u,v`)
parametrises the surface: the substitution of its three affine coordinates `(χ₁/χ₄, χ₂/χ₄, χ₃/χ₄)`
into `K[x₀,x₁,x₂]` is the `K`-algebra map

`azTheta a b g : K[x₀,x₁,x₂] →ₐ[K] K(u,v)`,  `K(u,v) = FractionRing (MvPolynomial (Fin 2) K)`,

and `azU K`, `azV K` are the two coordinate functions `u`, `v` of the parametrising plane.

## Why this file exists

These definitions were introduced in `Submission/Work/MotAS/censusAS2_junk_fwVec0.lean`, together
with the assembly of the census conjunct `Work.MotAS.censusAS2_junk_fwVec0`.  That assembly needs the
four lemmas `azFracRange`, `azTheta_fwVecAS2`, `azKerHeight`, `azPrimeFwVec0` (all stated in terms of
`azTheta`/`azU`/`azV`), so its file must *import* them; but they in turn must import the file holding
the definitions.  The result is an import cycle, which is broken by moving the definitions here,
strictly upstream of every one of those lemmas.  The consumers therefore import *this* module, and
`censusAS2_junk_fwVec0.lean` keeps only its assembly (§1, §3 and the `azE`-related lemmas) and
imports this one.

`azE` is deliberately **not** moved here: the name `Work.MotAS.azE` is already used for a scalar by
`Submission/Work/MotAS/AzDefs.lean` (the normal form of `fwVecAS2 · 0`), so keeping the vector
version `azE` — and the three lemmas mentioning it (`kleinQAS_azE`, `pAS0_eq_azE3`,
`kleinStereoAS_smul`) — in `censusAS2_junk_fwVec0.lean` avoids a name clash with `AzDefs`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Work.MotAS

variable {R : Type*} [CommRing R]

variable {K : Type*} [Field K]

/-- **The parametrising plane of `{f̂₀ = 0}`.**  The target plane `{ẑ₀ = 0, ẑ₄ = 0}` in the affine
chart `ẑ₃ = 1`, with coordinates `(u,v)`. -/
def azPlane (u v : R) : Fin 5 → R := ![0, u, v, 1, 0]

@[simp] theorem azPlane_zero (u v : R) : azPlane u v 0 = 0 := rfl
@[simp] theorem azPlane_one (u v : R) : azPlane u v 1 = u := rfl
@[simp] theorem azPlane_two (u v : R) : azPlane u v 2 = v := rfl
@[simp] theorem azPlane_three (u v : R) : azPlane u v 3 = 1 := rfl
@[simp] theorem azPlane_four (u v : R) : azPlane u v 4 = 0 := rfl

/-- The parametrising plane `(0,u,v,1,0)`, as a vector of the polynomial ring `K[u,v]`. -/
noncomputable def azP (K : Type*) [Field K] : Fin 5 → MvPolynomial (Fin 2) K :=
  azPlane (MvPolynomial.X 0) (MvPolynomial.X 1)

/-- The target point `R^AS(0,u,v,1,0)` of the inverse chart map, in `K[u,v]`. -/
noncomputable def azZ (a b g : K) : Fin 5 → MvPolynomial (Fin 2) K :=
  kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (azP K)

/-- The source point `χ = π_{pAS0}(R^AS(0,u,v,1,0))` of the inverse chart map, in `K[u,v]`
(`χ₀ = 0`: the projection lands in the source hyperplane `{v₀ = 0}`). -/
noncomputable def azChi (a b g : K) : Fin 5 → MvPolynomial (Fin 2) K :=
  ![0, azZ a b g 1, azZ a b g 2, azZ a b g 3, azZ a b g 4]

/-- **The parametrisation of `{f̂₀ = 0}`**: the three affine coordinates `χ₊₁/χ₄` of the inverse
chart map on the target plane, as elements of the fraction field `K(u,v)`. -/
noncomputable def azParam (a b g : K) : Fin 3 → FractionRing (MvPolynomial (Fin 2) K) :=
  ![algebraMap _ _ (azChi a b g 1) * (algebraMap _ _ (azChi a b g 4))⁻¹,
    algebraMap _ _ (azChi a b g 2) * (algebraMap _ _ (azChi a b g 4))⁻¹,
    algebraMap _ _ (azChi a b g 3) * (algebraMap _ _ (azChi a b g 4))⁻¹]

/-- **The presentation map of the surface `{f̂₀ = 0}`**: substitution of the parametrisation into
`K[x₀,x₁,x₂]`. -/
noncomputable def azTheta (a b g : K) :
    MvPolynomial (Fin 3) K →ₐ[K] FractionRing (MvPolynomial (Fin 2) K) :=
  MvPolynomial.aeval (azParam a b g)

/-- The first coordinate function `u` on the parametrising plane. -/
noncomputable def azU (K : Type*) [Field K] : FractionRing (MvPolynomial (Fin 2) K) :=
  algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (MvPolynomial.X 0)

/-- The second coordinate function `v` on the parametrising plane. -/
noncomputable def azV (K : Type*) [Field K] : FractionRing (MvPolynomial (Fin 2) K) :=
  algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (MvPolynomial.X 1)

@[simp] theorem azP_zero (K : Type*) [Field K] : azP K 0 = 0 := rfl
@[simp] theorem azP_one (K : Type*) [Field K] : azP K 1 = MvPolynomial.X 0 := rfl
@[simp] theorem azP_two (K : Type*) [Field K] : azP K 2 = MvPolynomial.X 1 := rfl
@[simp] theorem azP_three (K : Type*) [Field K] : azP K 3 = 1 := rfl
@[simp] theorem azP_four (K : Type*) [Field K] : azP K 4 = 0 := rfl

@[simp] theorem azChi_zero (a b g : K) : azChi a b g 0 = 0 := rfl
@[simp] theorem azChi_one (a b g : K) : azChi a b g 1 = azZ a b g 1 := rfl
@[simp] theorem azChi_two (a b g : K) : azChi a b g 2 = azZ a b g 2 := rfl
@[simp] theorem azChi_three (a b g : K) : azChi a b g 3 = azZ a b g 3 := rfl
@[simp] theorem azChi_four (a b g : K) : azChi a b g 4 = azZ a b g 4 := rfl

theorem azTheta_X (a b g : K) (i : Fin 3) :
    azTheta a b g (MvPolynomial.X i) = azParam a b g i := by
  simp only [azTheta, MvPolynomial.aeval_X]

end Work.MotAS
