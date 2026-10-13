/-
# `Work.FTS.Physical.Pressure.CurlCLM` — the curl as a continuous linear map of the derivative

`FiniteTimeSingularity.vorticity u x = ∑ i, eᵢ × (Du(x) eᵢ)` is a fixed *linear* function of the
Fréchet derivative `Du(x)`.  This module isolates that function as a continuous linear map

  `curlCLM : (ℝ³ →L[ℝ] ℝ³) →L[ℝ] ℝ³`

together with its "coordinate" form `curlOf` (the same function written with the standard basis and
the canonical identification `euclidEquiv : ℝ³ ≃L[ℝ] (Fin 3 → ℝ)`).  The two consequences used by
the pressure reconstruction of `Physical/Pressure.lean` are

* `vorticity_eq_curlCLM  :  vorticity u x = curlCLM (fderiv ℝ u x)` — the definition unfolded;
* `curlCLM_eq_curlOf` — the same element, in the form in which the linear-algebra identity
  `Work.FTS.Physical.Pressure.curlCompSelf` is consumed.

Being a continuous linear map, `curlCLM` is differentiable with itself as derivative
(`ContinuousLinearMap.hasFDerivAt`) and additive (`map_add`), which is what makes the product rule
for the curl of the material acceleration (`vorticity_materialAccel_eq`) a matter of the chain rule
for `HasFDerivAt`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure

/-- The canonical continuous linear identification `ℝ³ ≃L[ℝ] (Fin 3 → ℝ)`: its underlying
function is `WithLp.ofLp`. -/
noncomputable abbrev euclidEquiv : R3 ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ

/-- `WithLp.ofLp` as a continuous linear map `ℝ³ →L[ℝ] (Fin 3 → ℝ)`. -/
noncomputable abbrev ofLpCLM : R3 →L[ℝ] (Fin 3 → ℝ) := (euclidEquiv : R3 →L[ℝ] (Fin 3 → ℝ))

/-- `WithLp.toLp 2` as a continuous linear map `(Fin 3 → ℝ) →L[ℝ] ℝ³`. -/
noncomputable abbrev toLpCLM : (Fin 3 → ℝ) →L[ℝ] R3 := (euclidEquiv.symm : (Fin 3 → ℝ) →L[ℝ] R3)

theorem ofLpCLM_apply (x : R3) : ofLpCLM x = x.ofLp := rfl

theorem toLpCLM_apply (X : Fin 3 → ℝ) : toLpCLM X = WithLp.toLp 2 X := rfl

theorem toLpCLM_eq_equiv_symm (X : Fin 3 → ℝ) :
    toLpCLM X = (EuclideanSpace.equiv (Fin 3) ℝ).symm X := rfl

/-- `WithLp.toLp 2` commutes with the (three-term) sum in the definition of the curl. -/
theorem toLp_sum3 (f : Fin 3 → (Fin 3 → ℝ)) :
    WithLp.toLp 2 (∑ i, f i) = ∑ i, WithLp.toLp 2 (f i) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp

/-- The continuous linear map `v ↦ a × v` on `ℝ³`. -/
noncomputable def crossCLM (a : R3) : R3 →L[ℝ] R3 :=
  toLpCLM.comp (((crossProduct a.ofLp).toContinuousLinearMap).comp ofLpCLM)

theorem crossCLM_apply (a v : R3) : crossCLM a v = WithLp.toLp 2 (a ⨯₃ v) := by
  simp only [crossCLM, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    ofLpCLM_apply, toLpCLM_apply]

/-- **The curl as a continuous linear map of the derivative**:
`curlCLM T = ∑ i, eᵢ × (T eᵢ)`. -/
noncomputable def curlCLM : (R3 →L[ℝ] R3) →L[ℝ] R3 :=
  ∑ i : Fin 3, (crossCLM (FiniteTimeSingularity.e i)).comp
    (ContinuousLinearMap.apply ℝ R3 (FiniteTimeSingularity.e i))

/-- The same function as `curlCLM`, written with the standard basis and the canonical
identification `euclidEquiv : ℝ³ ≃L[ℝ] (Fin 3 → ℝ)`. -/
noncomputable def curlOf (T : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2
    ((∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ (T (FiniteTimeSingularity.e i))) : Fin 3 → ℝ)

theorem curlOf_apply (T : R3 →L[ℝ] R3) :
    curlOf T =
      WithLp.toLp 2 (∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ (T (FiniteTimeSingularity.e i))) :=
  rfl

theorem curlCLM_eq_curlOf (T : R3 →L[ℝ] R3) : curlCLM T = curlOf T := by
  have h1 : curlCLM T =
      ∑ i : Fin 3,
        WithLp.toLp 2 (FiniteTimeSingularity.e i ⨯₃ (T (FiniteTimeSingularity.e i))) := by
    simp only [curlCLM, sum_apply, ContinuousLinearMap.comp_apply, crossCLM_apply,
      ContinuousLinearMap.apply_apply]
  rw [h1, curlOf_apply, toLp_sum3]

/-- `vorticity u x = curlCLM (fderiv ℝ u x)`: the definition of the curl, with the sum of cross
products repackaged as a continuous linear map of the derivative. -/
theorem vorticity_eq_curlCLM (u : R3 → R3) (x : R3) :
    vorticity u x = curlCLM (fderiv ℝ u x) := by
  rw [curlCLM_eq_curlOf, curlOf_apply]
  rfl

/-- `curlOf` in the form of the linear-algebra identity `curlCompSelf`. -/
theorem curlOf_eq_symm (T : R3 →L[ℝ] R3) :
    curlOf T =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        (∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ (T (FiniteTimeSingularity.e i))) := by
  rw [curlOf_apply]
  rfl

/-- The composite form of `curlOf`, used to feed the linear-algebra identity. -/
theorem curlOf_comp (A B : R3 →L[ℝ] R3) :
    curlOf (A.comp B) =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        (∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ (A (B (FiniteTimeSingularity.e i)))) := by
  have h : (∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ ((A.comp B) (FiniteTimeSingularity.e i)))
      = ∑ i : Fin 3, FiniteTimeSingularity.e i ⨯₃ (A (B (FiniteTimeSingularity.e i))) :=
    Finset.sum_congr rfl fun i _ => by rw [ContinuousLinearMap.comp_apply]
  rw [curlOf_eq_symm, h]

end Work.FTS.Physical.Pressure
