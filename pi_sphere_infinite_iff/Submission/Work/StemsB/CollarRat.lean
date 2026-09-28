import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.StemsB.CollarModel

/-!
# The collar pair over `ℚ`

`Work.StemsB.serreSphere_collar_iso` computes the *integral* relative homology of the collar pair
`(sphLoopBig b × Y, sphLoopCollarProd b Y)`: it is `H_j(Y;ℤ)` in degree `j + b`, and it vanishes
below degree `b` (`Work.StemsB.serreSphere_collar_isZero`).  This file transports both statements to
`ℚ` coefficients by the flat base change `- ⊗[ℤ] ℚ` (`Work.StemsB.relChainsBaseChangeRat`), and then
computes the **relative cohomology** of the collar pair over `ℚ` by field duality:

* `homology_collar_iso_rat`, `homology_collar_isZero_rat` — the homological statements over `ℚ`;
* `relCohomology_dual_rat` — over a field (here `ℚ`), relative cohomology is the dual of relative
  homology (the two halves being `Work.StemsB.relComplexIsoDualR` and `Work.StemsB.ratDualUCT`);
* `cohomology_collar_iso_rat`, `cohomology_collar_isZero_rat` — the *cohomological* collar pair over
  `ℚ`, which is the single geometric input of the rational Wang sequence over a sphere (the `τ`
  identification of the E4 chapter, over `ℚ` instead of `ℤ`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Work.StemsB

noncomputable section

open Work.Cohomology

/-! ## Some `IsZero` arithmetic for duals -/

/-- The dual of a zero module is zero. -/
theorem isZero_hom_of_isZero (M : ModuleCat.{0} ℚ) (hM : IsZero M) :
    IsZero (ModuleCat.of ℚ (↥M →ₗ[ℚ] ℚ)) := by
  haveI : Subsingleton ↥M := ModuleCat.subsingleton_of_isZero hM
  haveI : Subsingleton (↥M →ₗ[ℚ] ℚ) :=
    ⟨fun f g => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-! ## The homological collar pair over `ℚ` -/

/-- **The relative homology of the collar pair over `ℚ`, above the dimension.** -/
theorem homology_collar_iso_rat (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (j : ℕ) :
    Nonempty (((relChainsR ℚ (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y)).homology (j + b)) ≅
      ((singularChains ℚ (TopCat.of Y)).homology j)) := by
  haveI : PreservesFiniteLimits IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits IntRatF := inferInstance
  haveI : IntRatF.PreservesHomology := inferInstance
  obtain ⟨eC⟩ := relChainsBaseChangeRat (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)
  obtain ⟨eZ⟩ := serreSphere_collar_iso b hb Y j
  exact ⟨(HomologicalComplex.homologyMapIso eC (j + b)).symm ≪≫
    (SphRat.homologyMapBaseChange IntRatF
      (relChains (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)) (j + b)).some ≪≫
    IntRatF.mapIso eZ ≪≫
    (SphRat.homologyMapBaseChange IntRatF (singularChains ℤ (TopCat.of Y)) j).some.symm ≪≫
    HomologicalComplex.homologyMapIso
      (RatBC.Phi (TopCat.toSSet.obj (TopCat.of Y))) j⟩

/-- **The relative homology of the collar pair over `ℚ` vanishes below the dimension.** -/
theorem homology_collar_isZero_rat (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (hm : m < b) :
    IsZero ((relChainsR ℚ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y)).homology m) := by
  haveI : PreservesFiniteLimits IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits IntRatF := inferInstance
  haveI : IntRatF.PreservesHomology := inferInstance
  obtain ⟨eC⟩ := relChainsBaseChangeRat (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)
  have hZ : IsZero ((relChains (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y)).homology m) := serreSphere_collar_isZero b hb Y m hm
  have hFZ : IsZero ((IntRatF.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (relChains (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)) |>.homology m) :=
    IsZero.of_iso (Functor.map_isZero IntRatF hZ)
      (SphRat.homologyMapBaseChange IntRatF
        (relChains (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)) m).some
  exact IsZero.of_iso hFZ (HomologicalComplex.homologyMapIso eC m).symm

/-! ## Relative cohomology over a field is the dual of relative homology -/

/-- **Over `ℚ`, relative cohomology is the dual of relative homology.**  This is the composition of
`Work.StemsB.relComplexIsoDualR` (relative cochains are the duals of the relative chains) with the
field universal coefficient theorem `Work.StemsB.ratDualUCT`. -/
theorem relCohomology_dual_rat (X : TopCat) (A : Set X) (n : ℕ) :
    Nonempty (((relComplex ℚ X A).homology n) ≅
      ModuleCat.of ℚ (↥((relChainsR ℚ X A).homology n) →ₗ[ℚ] ℚ)) := by
  obtain ⟨e₁⟩ := relComplexIsoDualR ℚ X A
  obtain ⟨e₂⟩ := ratDualUCT (relChainsR ℚ X A) n
  exact ⟨HomologicalComplex.homologyMapIso e₁ n ≪≫ e₂⟩

/-! ## The cohomological collar pair over `ℚ` -/

/-- **The relative cohomology of the collar pair over `ℚ`, above the dimension.** -/
theorem cohomology_collar_iso_rat (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (j : ℕ) :
    Nonempty (((relComplex ℚ (TopCat.of (↥(sphLoopBig b) × Y))
        (sphLoopCollarProd b Y)).homology (j + b)) ≅
      ((singularCochainComplex ℚ (TopCat.of Y)).homology j)) := by
  obtain ⟨e₁⟩ := relCohomology_dual_rat (TopCat.of (↥(sphLoopBig b) × Y))
    (sphLoopCollarProd b Y) (j + b)
  obtain ⟨e₂⟩ := homology_collar_iso_rat b hb Y j
  obtain ⟨e₃⟩ := fieldDualUCT ℚ (singularChains ℚ (TopCat.of Y)) j
  exact ⟨e₁ ≪≫ LinearEquiv.toModuleIso
      (LinearEquiv.dualMap (e₂.toLinearEquiv.symm)) ≪≫ e₃.symm⟩

/-- **The relative cohomology of the collar pair over `ℚ` vanishes below the dimension.** -/
theorem cohomology_collar_isZero_rat (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (m : ℕ) (hm : m < b) :
    IsZero ((relComplex ℚ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y)).homology m) := by
  obtain ⟨e₁⟩ := relCohomology_dual_rat (TopCat.of (↥(sphLoopBig b) × Y))
    (sphLoopCollarProd b Y) m
  exact IsZero.of_iso (isZero_hom_of_isZero _
    (homology_collar_isZero_rat b hb Y m hm)) e₁

end

end Work.StemsB
