import Mathlib
import Submission.Work.FFResidual.Kummer.Order
import Submission.Work.SilvermanReduction.hasGoodReduction_baseChange
import Submission.Work.TorsorExistence.Tate.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Good reduction of the constant Tate normal form at the Kummer place

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field over its constants with uniformizer
`π`, and let `R[s] = KummerOrder P = R[X]/(X ^ 5 - π)` be the Eisenstein order of the Kummer
extension `𝕜(s)`, `s ^ 5 = π` (`Submission/Work/FFResidual/Kummer/Order.lean`).  This file proves
that the **constant** Tate normal form

`E(c) : y² + (1 - c)xy - cy = x³ - cx²`,  `c ∈ 𝔽`,

base changed to the top field `𝕜(s)`, has good reduction at the place `R[s]`.

The point is that the coefficients of `E(c)` are images of constants: `1 - c`, `-c`, `-c`, `0`, `0`
all come from `𝔽 → R[s]`, so the model `E(c)` itself (with coefficients read in `R[s]`) is an
integral model over the Eisenstein order; its discriminant

`Δ = c⁵ (c² - 11 c - 1) ∈ 𝔽`

is a nonzero constant, hence a **unit** of `R[s]`, so the valuation of `Δ` is `1` — the top of the
value group `{v // v ≤ 1}`.  An integral model whose discriminant has valuation `1` is minimal
(`WeierstrassCurve.valuation_Δ_aux` takes values in that subtype) and has good reduction
(`Work.SilvermanReduction.hasGoodReduction_of_valuation_Δ_eq_one'`).

Geometrically: the constant curve `E(c)` acquires an integral model with unit discriminant at the
Kummer place, so reduction at that place does not degenerate.

## Main results

* `FunctionFieldPlace.algebraMap_KummerOrder_comp_algebraMap` — the structure maps `𝔽 → R[s] → 𝕜(s)`
  and `𝔽 → 𝕜(s)` agree.
* `FunctionFieldPlace.isUnit_algebraMap_KummerOrder` — a nonzero constant is a unit of the
  Eisenstein order.
* `Work.FFResidual.Kummer.hasGoodReduction_kummerOrder` — the theorem.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.FFResidual

noncomputable section

open WeierstrassCurve

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

namespace FunctionFieldPlace

/-- The structure maps of the Kummer extension agree: `𝔽 → R[s] → 𝕜(s)` is the structure map
`𝔽 → 𝕜(s)` of the top field. -/
theorem algebraMap_KummerOrder_comp_algebraMap (P : FunctionFieldPlace 𝔽 𝕜) :
    (algebraMap P.KummerOrder P.Top).comp (algebraMap 𝔽 P.KummerOrder) =
      algebraMap 𝔽 P.Top := by
  ext x
  exact P.kummerOrderMap_algebraMap_𝔽 x

/-- A nonzero constant is a unit of the Eisenstein order `R[s]`: along `𝔽 → R → R[s]` it is the
image of the unit `x` of the field `𝔽`. -/
theorem isUnit_algebraMap_KummerOrder (P : FunctionFieldPlace 𝔽 𝕜) (x : 𝔽) (hx : x ≠ 0) :
    IsUnit (algebraMap 𝔽 P.KummerOrder x) := by
  rw [algebraMap_𝔽_KummerOrder, ← AdjoinRoot.algebraMap_eq]
  exact (P.isUnit_algebraMap x hx).map _

end FunctionFieldPlace

namespace Kummer

/-- **The constant Tate normal form has good reduction at the Kummer place.**  The coefficients of
the base-changed Tate model `E(c) = y² + (1-c)xy - cy = x³ - cx²` over the top field `𝕜(s)` are the
images of constants `𝔽 → R → 𝔽 ⊆ R`, hence units of the Eisenstein order `R[s]`, and its
discriminant is a unit; so the model is integral with unit discriminant at the place. -/
theorem hasGoodReduction_kummerOrder {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝔽 𝕜] (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜)
    [IsDomain (Work.FFResidual.FunctionFieldPlace.KummerOrder P)]
    [IsDiscreteValuationRing (Work.FFResidual.FunctionFieldPlace.KummerOrder P)]
    [IsFractionRing (Work.FFResidual.FunctionFieldPlace.KummerOrder P) P.Top]
    (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    WeierstrassCurve.HasGoodReduction (Work.FFResidual.FunctionFieldPlace.KummerOrder P)
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.Top) := by
  -- The structure maps `𝔽 → R[s] → 𝕜(s)` and `𝔽 → 𝕜(s)` agree, so the base-changed curve is the
  -- base change of the model `E(c)` over the Eisenstein order `R[s]`.
  have hcomp := FunctionFieldPlace.algebraMap_KummerOrder_comp_algebraMap P
  have hW : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.Top
      = ((Work.TorsorExistence.Tate.tateCurve c).map (algebraMap 𝔽 P.KummerOrder)).map
          (algebraMap P.KummerOrder P.Top) := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rw [hcomp]
    rfl
  -- `Δ` of the model over `R[s]` is the image of the nonzero constant `Δ_{E(c)}`, hence a unit.
  have hunit : IsUnit ((Work.TorsorExistence.Tate.tateCurve c).map
      (algebraMap 𝔽 P.KummerOrder)).Δ := by
    rw [WeierstrassCurve.map_Δ]
    exact FunctionFieldPlace.isUnit_algebraMap_KummerOrder P _ hΔ
  -- Hence the model is integral over `R[s]` …
  have hInt : WeierstrassCurve.IsIntegral P.KummerOrder
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.Top) :=
    ⟨(Work.TorsorExistence.Tate.tateCurve c).map (algebraMap 𝔽 P.KummerOrder), hW⟩
  haveI := hInt
  -- … its discriminant is the image of that unit …
  have hΔW : (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.Top).Δ
      = algebraMap P.KummerOrder P.Top ((Work.TorsorExistence.Tate.tateCurve c).map
          (algebraMap 𝔽 P.KummerOrder)).Δ := by
    rw [hW, WeierstrassCurve.map_Δ]
  -- … so its valuation at the maximal ideal is `1`, the top of the value group.
  have hval : (IsDedekindDomain.HeightOneSpectrum.valuation P.Top
      (IsDiscreteValuationRing.maximalIdeal P.KummerOrder))
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.Top).Δ = 1 := by
    rw [hΔW, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    simp only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.notMem_maximalIdeal]
    exact hunit
  exact Work.SilvermanReduction.hasGoodReduction_of_valuation_Δ_eq_one' P.KummerOrder hval

end Kummer

end

end Work.FFResidual
