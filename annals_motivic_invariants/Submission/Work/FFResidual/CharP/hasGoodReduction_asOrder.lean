import Mathlib
import Submission.Work.FFResidual.CharP.Order
import Submission.Work.SilvermanReduction.hasGoodReduction_baseChange
import Submission.Work.TorsorExistence.Tate.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Good reduction of the constant Tate normal form at the Artin–Schreier place

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field over its constants with uniformizer
`π`, in characteristic `5`, and let `R[w] = AsOrder P = R[X]/(X ^ 5 + π X ^ 4 - π)` be the
Eisenstein order of the Artin–Schreier extension `𝕜(s)`, `s ^ 5 - s = π⁻¹`
(`Submission/Work/FFResidual/CharP/Order.lean`).  This file proves that the **constant** Tate
normal form

`E(c) : y² + (1 - c)xy - cy = x³ - cx²`,  `c ∈ 𝔽`,

base changed to the top field `𝕜(s)`, has good reduction at the place `R[w]`.

## Main results

* `FunctionFieldPlace.algebraMap_AsOrder_comp_algebraMap` — the structure maps `𝔽 → R[w] → 𝕜(s)`
  and `𝔽 → 𝕜(s)` agree.
* `FunctionFieldPlace.isUnit_algebraMap_AsOrder` — a nonzero constant is a unit of the
  Artin–Schreier order.
* `Work.FFResidual.CharP.hasGoodReduction_asOrder` — the theorem.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.FFResidual

noncomputable section

open WeierstrassCurve

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

namespace FunctionFieldPlace

/-- The structure maps of the Artin–Schreier extension agree: `𝔽 → R[w] → 𝕜(s)` is the structure
map `𝔽 → 𝕜(s)` of the top field. -/
theorem algebraMap_AsOrder_comp_algebraMap (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    (algebraMap P.AsOrder P.AsTop).comp (algebraMap 𝔽 P.AsOrder) =
      algebraMap 𝔽 P.AsTop := by
  ext x
  rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
  exact P.asOrderMap_algebraMap_𝔽 x

/-- A nonzero constant is a unit of the Artin–Schreier order `R[w]`: along `𝔽 → R → R[w]` it is the
image of the unit `x` of the field `𝔽`. -/
theorem isUnit_algebraMap_AsOrder (P : FunctionFieldPlace 𝔽 𝕜) (x : 𝔽) (hx : x ≠ 0) :
    IsUnit (algebraMap 𝔽 P.AsOrder x) := by
  rw [algebraMap_𝔽_AsOrder, ← AdjoinRoot.algebraMap_eq]
  exact (P.isUnit_algebraMap x hx).map _

end FunctionFieldPlace

namespace CharP

/-- **The constant Tate normal form has good reduction at the Artin–Schreier place.**  The
coefficients of the base-changed Tate model over `AsTop = 𝕜(s)`, `s ^ 5 - s = π⁻¹`, are the images
of the constants `𝔽 → R`, hence units of the Artin–Schreier order `R[w]`, and its discriminant is a
unit; so the model is integral with unit discriminant at the place. -/
theorem hasGoodReduction_asOrder {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]
    (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5]
    [IsDomain (Work.FFResidual.FunctionFieldPlace.AsOrder P)]
    [IsDiscreteValuationRing (Work.FFResidual.FunctionFieldPlace.AsOrder P)]
    [IsFractionRing (Work.FFResidual.FunctionFieldPlace.AsOrder P) P.AsTop]
    (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    WeierstrassCurve.HasGoodReduction (Work.FFResidual.FunctionFieldPlace.AsOrder P)
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.AsTop) := by
  -- The structure maps `𝔽 → R[w] → 𝕜(s)` and `𝔽 → 𝕜(s)` agree, so the base-changed curve is the
  -- base change of the model `E(c)` over the Artin–Schreier order `R[w]`.
  have hcomp := FunctionFieldPlace.algebraMap_AsOrder_comp_algebraMap P
  have hW : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.AsTop
      = ((Work.TorsorExistence.Tate.tateCurve c).map (algebraMap 𝔽 P.AsOrder)).map
          (algebraMap P.AsOrder P.AsTop) := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rw [hcomp]
    rfl
  -- `Δ` of the model over `R[w]` is the image of the nonzero constant `Δ_{E(c)}`, hence a unit.
  have hunit : IsUnit ((Work.TorsorExistence.Tate.tateCurve c).map
      (algebraMap 𝔽 P.AsOrder)).Δ := by
    rw [WeierstrassCurve.map_Δ]
    exact FunctionFieldPlace.isUnit_algebraMap_AsOrder P _ hΔ
  -- Hence the model is integral over `R[w]` …
  have hInt : WeierstrassCurve.IsIntegral P.AsOrder
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.AsTop) :=
    ⟨(Work.TorsorExistence.Tate.tateCurve c).map (algebraMap 𝔽 P.AsOrder), hW⟩
  haveI := hInt
  -- … its discriminant is the image of that unit …
  have hΔW : (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.AsTop).Δ
      = algebraMap P.AsOrder P.AsTop ((Work.TorsorExistence.Tate.tateCurve c).map
          (algebraMap 𝔽 P.AsOrder)).Δ := by
    rw [hW, WeierstrassCurve.map_Δ]
  -- … so its valuation at the maximal ideal is `1`, the top of the value group.
  have hval : (IsDedekindDomain.HeightOneSpectrum.valuation P.AsTop
      (IsDiscreteValuationRing.maximalIdeal P.AsOrder))
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.AsTop).Δ = 1 := by
    rw [hΔW, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    simp only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.notMem_maximalIdeal]
    exact hunit
  exact Work.SilvermanReduction.hasGoodReduction_of_valuation_Δ_eq_one' P.AsOrder hval

end CharP

end

end Work.FFResidual
