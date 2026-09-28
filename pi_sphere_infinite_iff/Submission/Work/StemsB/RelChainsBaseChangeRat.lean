import Submission.Work.StemsB.RatBaseNaturality
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Cohomology.HomologyPairSequence

/-!
# Base change of the relative singular chains, `ℤ → ℚ`

`C_*(X,A;ℤ)` is the cokernel of the inclusion `C_*(A;ℤ) ⟶ C_*(X;ℤ)`, and `C_*(X,A;ℚ)` is the
cokernel of the inclusion over `ℚ`.  Since `- ⊗[ℤ] ℚ` is a right exact functor, it carries the first
cokernel to the second:

  `relChainsBaseChangeRat : (C_*(X,A;ℤ) ⊗[ℤ] ℚ) ≅ C_*(X,A;ℚ)`.

This is the comparison that lets a *homological* computation over `ℤ` be consumed over `ℚ`, and it is
the missing link between the `ℤ`-coefficient Wang/collar chapter of this directory and the
`ℚ`-coefficient statements subproject SERRE's engine needs.

The proof is the one recorded in `Submission/Work/Stems/Engine/CoeffTransfer.lean`: the naturality
`Work.StemsB.RatBC.Phi_naturality` of the base change in the space identifies the two inclusions,
`PreservesCokernel.iso` moves the base change inside the first cokernel, and `cokernel.mapIso`
identifies the two cokernels.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Work.StemsB

noncomputable section

abbrev IntRatF : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ :=
  ModuleCat.extendScalars (Int.castRingHom ℚ)

abbrev IntRatCM : ChainComplex (ModuleCat.{0} ℤ) ℕ ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  IntRatF.mapHomologicalComplex (ComplexShape.down ℕ)

/-- **Base change of the relative singular chains.** -/
theorem relChainsBaseChangeRat (X : TopCat) (A : Set X) :
    Nonempty ((IntRatCM.obj (Work.Cohomology.relChains X A)) ≅ relChainsR ℚ X A) := by
  haveI : PreservesFiniteLimits IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits IntRatF := inferInstance
  haveI : IntRatF.PreservesHomology := inferInstance
  haveI : PreservesFiniteColimits IntRatCM := inferInstance
  haveI : PreservesFiniteLimits IntRatCM := inferInstance
  -- the two inclusions are identified by the naturality of the base change
  have hsq : IntRatCM.map (Work.Cohomology.inclChains X A)
      ≫ (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom
      = (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A))).hom
      ≫ relChainsRIncl ℚ X A := by
    show (Work.StemsB.RatBC.IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
          (Functor.whiskerRight (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
            (Limits.sigmaConst.obj Work.StemsB.RatBC.ZMod)))
        ≫ (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom
      = (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A))).hom
        ≫ (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
          (Functor.whiskerRight (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
            (Limits.sigmaConst.obj Work.StemsB.RatBC.QMod))
    exact (Work.StemsB.RatBC.Phi_naturality
      (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))).symm
  exact ⟨Limits.PreservesCokernel.iso IntRatCM (Work.Cohomology.inclChains X A) ≪≫
    Limits.cokernel.mapIso (IntRatCM.map (Work.Cohomology.inclChains X A))
      (relChainsRIncl ℚ X A)
      (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A)))
      (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)) hsq⟩

end

end Work.StemsB
