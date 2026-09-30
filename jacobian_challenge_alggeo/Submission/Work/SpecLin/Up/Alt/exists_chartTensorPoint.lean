/-
# Namespace mirror of `Work.SpecLin.Alt.exists_chartTensorPoint`

This file is an exact copy of `Submission/Work/SpecLin/Alt/exists_chartTensorPoint.lean` (module `Work.SpecLin.Alt.exists_chartTensorPoint`), changed in exactly three ways:

* a `namespace Up` / `end Up` pair is inserted immediately inside the file's own namespace, so
  that every declaration `Work.SpecLin.<Area>.<x>` of the original appears here as
  `Work.SpecLin.<Area>.Up.<x>` (this avoids a name clash with the original, which cannot be
  removed: the original is part of the shared library);
* references to declarations *of the mirrored modules* are rewritten accordingly (full and
  area-relative forms), and imports of those modules point at their mirrors;
* an import of `Core/linEquiv_of_sections_of_chart.lean` (the module that *states* the
  affine-chart theorem) is replaced by an import of the upstream vocabulary module
  `Core/chartVocab.lean`, which declares the same chart algebra under the same names.

The point of the mirror is to break the import cycle
`vocabulary -> statement -> ... -> proof modules -> vocabulary`: the proof modules used to take
their vocabulary from the module that states the theorem, and this made a proof of that theorem
unreachable.  The mathematics is unchanged: the mirror is a verbatim copy of verified code.

The statements of the mirrored theorems mention only names that are *upstream* of the mirror, so
`Work.SpecLin.Core.Up.chartSpecialisation` (module
`Submission.Work.SpecLin.Up.Core.chartSpecialisation`) has literally the statement of
`Work.SpecLin.Core.linEquiv_of_sections_of_chart`, which is proved from it.
-/
import Mathlib
import Submission.Work.SpecLin.Up.Alt.chartMap
import Submission.Work.SpecLin.Up.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Up.Alt.isLocalization_chartTensorSectionsMap
import Submission.Work.SpecLin.Up.Alt.chartTensorPointSetup
import Submission.Work.SpecLin.Alt.exists_mul_eq_iff_of_isLocalization
import Submission.Work.SpecLin.Alt.mem_range_algebraMap_iff_exists_mul_eq
import Submission.Work.SpecLin.Setup.ord_eq_ordFrac_localization
import Submission.Work.CurveBasics.Curve.BCSquare.SectionsTensor
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt
namespace Up

theorem exists_chartTensorPoint {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (p : Ideal (Work.SpecLin.Core.chartTensor R W)) (hp : p.IsPrime) (hp1 : p.height = 1)
    (hmiss : ∀ r : R, r ≠ 0 → Algebra.TensorProduct.includeRight r ∉ p) :
    ∃ Q : (C.baseChange (FractionRing R)).Place,
      Q.point ∈ C.bcOpens (FractionRing R) W ∧
      (∀ x : (C.baseChange (FractionRing R)).functionField,
        (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ p ∧
            x * Work.SpecLin.Alt.Up.chartTensorMap R W hW b
              = Work.SpecLin.Alt.Up.chartTensorMap R W hW a)
          ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q) := by
  haveI hUaff : IsAffineOpen (C.bcOpens (FractionRing R) W) := chartAffineOpen R W hW
  haveI hp' : (chartTensorPrime R W hW p).IsPrime :=
    chartTensorPrime_isPrime R W hW p hp hmiss
  haveI hneU : Nonempty (C.bcOpens (FractionRing R) W) := C.bcOpens_nonempty (FractionRing R) W
  refine ⟨⟨chartTensorPoint R W hW p hp hmiss,
      chartTensorPoint_isClosed R W hW p hp hp1 hmiss⟩,
    chartTensorPoint_mem R W hW p hp hmiss, fun x => ?_⟩
  rw [← Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff]
  -- The two algebra structures on the chart ring of the generic fibre and on `K(C_F)`,
  -- both induced by the chart dictionary.
  letI : Algebra (Work.SpecLin.Core.chartTensor R W) (chartSections R W) :=
    (chartTensorSectionsMap R W hW).toAlgebra
  letI : Algebra (Work.SpecLin.Core.chartTensor R W)
      (C.baseChange (FractionRing R)).functionField :=
    (chartTensorMap R W hW).toAlgebra
  haveI hS : IsLocalization (chartContentSubmonoid (K := K) (C := C) R W) (chartSections R W) :=
    isLocalization_chartTensorSectionsMap R W hW
  haveI hST : IsScalarTower (Work.SpecLin.Core.chartTensor R W) (chartSections R W)
      (C.baseChange (FractionRing R)).functionField :=
    IsScalarTower.of_algebraMap_eq (fun b => rfl)
  -- Step 1: passing from the relative chart `B` to its localisation `S = Γ(C_F, W_F)`.
  have step1 : (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ p ∧
        x * chartTensorMap R W hW b = chartTensorMap R W hW a) ↔
      (∃ a b : chartSections R W, b ∉ chartTensorPrime R W hW p ∧
        x * algebraMap (chartSections R W)
              (C.baseChange (FractionRing R)).functionField b
          = algebraMap (chartSections R W)
              (C.baseChange (FractionRing R)).functionField a) :=
    exists_mul_eq_iff_of_isLocalization
      (chartContentSubmonoid (K := K) (C := C) R W) p
      (chartContentSubmonoid_disjoint R W p hmiss) x
  -- Step 2: passing from `S` to the local ring at the point.
  letI : Algebra (chartSections R W)
      (((C.baseChange (FractionRing R)).left).presheaf.stalk
        (chartTensorPoint R W hW p hp hmiss)) :=
    TopCat.Presheaf.algebra_section_stalk ((C.baseChange (FractionRing R)).left).presheaf
      ⟨chartTensorPoint R W hW p hp hmiss, chartTensorPoint_mem R W hW p hp hmiss⟩
  haveI hloc : IsLocalization.AtPrime
      (((C.baseChange (FractionRing R)).left).presheaf.stalk
        (chartTensorPoint R W hW p hp hmiss)) (chartTensorPrime R W hW p) :=
    hUaff.isLocalization_stalk'
      ⟨chartTensorPrime R W hW p, chartTensorPrime_isPrime R W hW p hp hmiss⟩
      (chartTensorPoint_mem R W hW p hp hmiss)
  haveI hST2 : IsScalarTower (chartSections R W)
      (((C.baseChange (FractionRing R)).left).presheaf.stalk
        (chartTensorPoint R W hW p hp hmiss))
      (C.baseChange (FractionRing R)).functionField :=
    functionField_isScalarTower (C.baseChange (FractionRing R)).left
      (C.bcOpens (FractionRing R) W)
      ⟨chartTensorPoint R W hW p hp hmiss, chartTensorPoint_mem R W hW p hp hmiss⟩
  rw [mem_range_algebraMap_iff_exists_mul_eq (chartTensorPrime R W hW p) x]
  exact step1

end Up
end Work.SpecLin.Alt

