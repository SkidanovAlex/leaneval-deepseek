/-
# The chart dictionary for `Work.SpecLin.Alt.chartCoreDiv`

For a curve `C` over a field `K`, a `K`-valuation ring `R` and an affine open chart `W ⊆ C` with
coordinate ring `A = Γ(C,W)`, this file defines the two canonical ring homomorphisms

* `chartTensorMap   : A ⊗_K R →+* K(C_F)`   (`F = FractionRing R`), and
* `chartTensorRedMap : A ⊗_K R →+* K(C_κ)`   (`κ = IsLocalRing.ResidueField R`)

from the coordinate ring `B = A ⊗_K R` of the "relative chart" `W ×_K Spec R` to the function
fields of the generic and the special fibre.  Both are the composite of

`B --Algebra.TensorProduct.map--> A ⊗_K L --sectionsLift--> Γ(C_L, W_L) --germ--> K(C_L)`

where `L = F` resp. `L = κ`, `sectionsLift` is the identification of the sections of the affine
chart of the base change with the tensor product (`Work.CurveBasics.Curve.BCSquare.sectionsLift`)
and `germ` is `Work.CurveBasics.Curve.germToFunctionField`.  The evaluation clauses on pure
tensors are proved below (`chartTensorMap_tmul_one`, `chartTensorMap_one_tmul`,
`chartTensorRedMap_tmul_one`, `chartTensorRedMap_one_tmul`).

These are the first half of the "chart dictionary" of `Alt/NOTES_chartCoreDiv.md`; the
fraction-ring/injectivity statements and the order/point dictionary are delegated to
`Submission/Work/SpecLin/Alt/chartMap*.lean`.
-/
import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Setup
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Alt.chartDictionary
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Content.isPrincipal_of_fg_of_cyclic_map_quotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

open Work.CurveBasics in
/-- **The chart dictionary: the relative chart `B = Γ(C,W) ⊗_K R` inside the function field of
the generic fibre.** -/
noncomputable def chartTensorMap (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W →+*
      (C.baseChange (FractionRing R)).functionField :=
  letI : Nonempty ((Curve.bcSquare C (FractionRing R)).π ⁻¹ᵁ W) :=
    Curve.BCSquare.instNonemptyPreimage _ W
  ((Curve.germToFunctionField (C.baseChange (FractionRing R))
      ((Curve.bcSquare C (FractionRing R)).π ⁻¹ᵁ W)).hom).comp
    (((Curve.BCSquare.sectionsLift (Curve.bcSquare C (FractionRing R)) W hW)).comp
      (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (FractionRing R))).toRingHom)

open Work.CurveBasics in
/-- **The chart dictionary: the relative chart `B = Γ(C,W) ⊗_K R` inside the function field of
the special fibre.** -/
noncomputable def chartTensorRedMap (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W →+*
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
  letI : Nonempty ((Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W) :=
    Curve.BCSquare.instNonemptyPreimage _ W
  ((Curve.germToFunctionField (C.baseChange (IsLocalRing.ResidueField R))
      ((Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W)).hom).comp
    (((Curve.BCSquare.sectionsLift (Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW)).comp
      (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))).toRingHom)

open Work.CurveBasics in
theorem chartTensorMap_tmul_one (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (a : Γ(C.left, W)) :
    chartTensorMap (K:=K) (C:=C) R W hW (a ⊗ₜ[K] (1 : R))
      = (Curve.functionFieldMap C (FractionRing R)).hom
          ((Curve.germToFunctionField C W).hom a) := by
  unfold chartTensorMap
  rw [RingHom.comp_apply, RingHom.comp_apply]
  rw [show (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (FractionRing R))).toRingHom (a ⊗ₜ[K] (1 : R))
      = (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (FractionRing R))) (a ⊗ₜ[K] (1 : R)) from rfl]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply, map_one]
  rw [Curve.BCSquare.sectionsLift_tmul_one]
  rw [← Curve.BCSquare.fieldMap_germToFunctionField_apply
    (C := C) (C' := C.baseChange (FractionRing R))
    (Curve.bcSquare C (FractionRing R)) W a]
  rfl

open Work.CurveBasics in
theorem chartTensorMap_one_tmul (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (r : R) :
    chartTensorMap (K:=K) (C:=C) R W hW ((1 : Γ(C.left,W)) ⊗ₜ[K] r)
      = algebraMap (FractionRing R) ((C.baseChange (FractionRing R)).functionField)
          (algebraMap R (FractionRing R) r) := by
  unfold chartTensorMap
  rw [RingHom.comp_apply, RingHom.comp_apply]
  rw [show (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (FractionRing R))).toRingHom ((1 : Γ(C.left,W)) ⊗ₜ[K] r)
      = (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (FractionRing R))) ((1 : Γ(C.left,W)) ⊗ₜ[K] r) from rfl]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
  rw [Curve.BCSquare.sectionsLift_one_tmul]
  rw [Curve.BCSquare.germToFunctionField_algebraMap]

open Work.CurveBasics in
theorem chartTensorRedMap_tmul_one (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (a : Γ(C.left, W)) :
    chartTensorRedMap (K:=K) (C:=C) R W hW (a ⊗ₜ[K] (1 : R))
      = (Curve.functionFieldMap C (IsLocalRing.ResidueField R)).hom
          ((Curve.germToFunctionField C W).hom a) := by
  unfold chartTensorRedMap
  rw [RingHom.comp_apply, RingHom.comp_apply]
  rw [show (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))).toRingHom (a ⊗ₜ[K] (1 : R))
      = (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))) (a ⊗ₜ[K] (1 : R)) from rfl]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply, map_one]
  rw [Curve.BCSquare.sectionsLift_tmul_one]
  rw [← Curve.BCSquare.fieldMap_germToFunctionField_apply
    (C := C) (C' := C.baseChange (IsLocalRing.ResidueField R))
    (Curve.bcSquare C (IsLocalRing.ResidueField R)) W a]
  rfl

open Work.CurveBasics in
theorem chartTensorRedMap_one_tmul (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (r : R) :
    chartTensorRedMap (K:=K) (C:=C) R W hW ((1 : Γ(C.left,W)) ⊗ₜ[K] r)
      = algebraMap (IsLocalRing.ResidueField R)
          ((C.baseChange (IsLocalRing.ResidueField R)).functionField)
          (algebraMap R (IsLocalRing.ResidueField R) r) := by
  unfold chartTensorRedMap
  rw [RingHom.comp_apply, RingHom.comp_apply]
  rw [show (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))).toRingHom
        ((1 : Γ(C.left,W)) ⊗ₜ[K] r)
      = (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))) ((1 : Γ(C.left,W)) ⊗ₜ[K] r)
      from rfl]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
  rw [Curve.BCSquare.sectionsLift_one_tmul]
  rw [Curve.BCSquare.germToFunctionField_algebraMap]

open Work.CurveBasics in
/-- The fibre prime `P = m_R·B` is contained in the kernel of the reduction map: reduction
modulo `P` kills the maximal ideal of `R`. -/
theorem chartFibrePrime_le_ker_redMap (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W
      ≤ RingHom.ker (chartTensorRedMap (K:=K) (C:=C) R W hW) := by
  rw [Work.SpecLin.Core.chartFibrePrime, Ideal.map_le_iff_le_comap]
  intro r hr
  show Algebra.TensorProduct.includeRight r ∈ RingHom.ker (chartTensorRedMap (K:=K) (C:=C) R W hW)
  rw [RingHom.mem_ker]
  rw [show (Algebra.TensorProduct.includeRight (R := K) (A := Γ(C.left, W)) (B := R)) r
        = ((1 : Γ(C.left, W)) ⊗ₜ[K] r) from by
    simp [Algebra.TensorProduct.includeRight_apply]]
  rw [chartTensorRedMap_one_tmul]
  rw [show algebraMap R (IsLocalRing.ResidueField R) r = 0 from by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact hr, map_zero]

open Work.CurveBasics in
/-- **The reduction map on the special fibre**, `B ⧸ P →+* K(C_κ)`. -/
noncomputable def chartFibreQuotMap (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    (Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W
        ⧸ Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) →+*
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
  Ideal.Quotient.lift _ (chartTensorRedMap (K:=K) (C:=C) R W hW)
    (chartFibrePrime_le_ker_redMap (K:=K) (C:=C) R W hW)

open Work.CurveBasics in
theorem chartFibreQuotMap_mk (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (x : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W) :
    chartFibreQuotMap (K:=K) (C:=C) R W hW
        (Ideal.Quotient.mk _ x)
      = chartTensorRedMap (K:=K) (C:=C) R W hW x :=
  rfl


open Work.CurveBasics in
/-- **The chart dictionary, sections form**: the `K`-algebra map from the relative chart
`B = Γ(C,W) ⊗_K R` to the sections `Γ(C_F, C.bcOpens F W)` of the affine chart of the generic
fibre.  It is `Algebra.TensorProduct.map (AlgHom.id) (R → F)` followed by `sectionsLift`. -/
noncomputable def chartTensorSectionsMap (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W →+*
      Γ((C.baseChange (FractionRing R)).left,
        (Curve.bcSquare C (FractionRing R)).π ⁻¹ᵁ W) :=
  letI : Nonempty ((Curve.bcSquare C (FractionRing R)).π ⁻¹ᵁ W) :=
    Curve.BCSquare.instNonemptyPreimage _ W
  (Curve.BCSquare.sectionsLift (Curve.bcSquare C (FractionRing R)) W hW).comp
    (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
      (IsScalarTower.toAlgHom K R (FractionRing R))).toRingHom

open Work.CurveBasics in
/-- **The chart dictionary, sections form**: the same map with the special fibre `κ` in place of
the generic fibre `F`. -/
noncomputable def chartTensorRedSectionsMap (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W →+*
      Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
        (Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W) :=
  letI : Nonempty ((Curve.bcSquare C (IsLocalRing.ResidueField R)).π ⁻¹ᵁ W) :=
    Curve.BCSquare.instNonemptyPreimage _ W
  (Curve.BCSquare.sectionsLift (Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW).comp
    (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))).toRingHom

open Work.CurveBasics in
theorem chartTensorMap_eq_germ_comp_sectionsMap (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    chartTensorMap (K:=K) (C:=C) R W hW
      = ((Curve.germToFunctionField (C.baseChange (FractionRing R))
          (C.bcOpens (FractionRing R) W)).hom).comp
        (chartTensorSectionsMap (K:=K) (C:=C) R W hW) := by
  rfl

open Work.CurveBasics in
theorem chartTensorRedMap_eq_germ_comp_sectionsMap (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    chartTensorRedMap (K:=K) (C:=C) R W hW
      = ((Curve.germToFunctionField (C.baseChange (IsLocalRing.ResidueField R))
          (C.bcOpens (IsLocalRing.ResidueField R) W)).hom).comp
        (chartTensorRedSectionsMap (K:=K) (C:=C) R W hW) := by
  rfl

open Work.CurveBasics in
theorem chartTensorSectionsMap_tmul_one (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (a : Γ(C.left, W)) :
    chartTensorSectionsMap (K:=K) (C:=C) R W hW (a ⊗ₜ[K] (1 : R))
      = (Curve.bcSquare C (FractionRing R)).π.app W a := by
  unfold chartTensorSectionsMap
  rw [RingHom.comp_apply]
  rw [show (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (FractionRing R))).toRingHom (a ⊗ₜ[K] (1 : R))
      = (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (FractionRing R))) (a ⊗ₜ[K] (1 : R)) from rfl]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply, map_one]
  rw [Curve.BCSquare.sectionsLift_tmul_one]

open Work.CurveBasics in
theorem chartTensorRedSectionsMap_tmul_one (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] (W : C.left.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (a : Γ(C.left, W)) :
    chartTensorRedSectionsMap (K:=K) (C:=C) R W hW (a ⊗ₜ[K] (1 : R))
      = (Curve.bcSquare C (IsLocalRing.ResidueField R)).π.app W a := by
  unfold chartTensorRedSectionsMap
  rw [RingHom.comp_apply]
  rw [show (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))).toRingHom (a ⊗ₜ[K] (1 : R))
      = (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left,W))
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))) (a ⊗ₜ[K] (1 : R)) from rfl]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply, map_one]
  rw [Curve.BCSquare.sectionsLift_tmul_one]


end Work.SpecLin.Alt
