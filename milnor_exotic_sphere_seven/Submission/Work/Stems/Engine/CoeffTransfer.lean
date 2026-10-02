import Submission.Work.Serre.C1Rat
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative coefficient transfer `ℤ → ℚ`

`Work.Cohomology.relChains X A = C_*(X,A;ℤ)` is the cokernel of the inclusion of the integral
singular chains of `A` into those of `X`; `Work.StemsB.relChainsR ℚ X A = C_*(X,A;ℚ)` is the same
construction over `ℚ`.  The engine of subproject SERRE produces *integral* vanishing (`SerreE2b`,
`SerreE2c`, `SerreE2d`), while `E3a`, `C1`, `C2`, `C3`, `S1` are stated over `ℚ`, so this transfer
is what lets the rational layer consume the integral one.

The proof uses the (proved) naturality of the base change `C_*(X;ℤ) ⊗[ℤ] ℚ ≅ C_*(X;ℚ)` in the
space, `Work.Serre.Phi_naturality`: `F = - ⊗[ℤ] ℚ` is right exact, so it carries the cokernel
defining `C_*(X,A;ℤ)` to the cokernel defining `C_*(X,A;ℚ)`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial TensorProduct

namespace Work.Stems.Engine

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- **The relative coefficient transfer.**  Vanishing of the integral relative homology in a degree
implies vanishing of the rational one. -/
theorem isZero_relChainsR_rat_of_isZero_relChains (X : TopCat) (A : Set X) (n : ℕ)
    (h : IsZero ((Work.Cohomology.relChains X A).homology n)) :
    IsZero ((Work.StemsB.relChainsR ℚ X A).homology n) := by
  let F : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ := Work.Serre.IntRat
  haveI hflat : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits F := inferInstance
  haveI : F.PreservesHomology := inferInstance
  -- the inclusion, as a map of simplicial sets
  let σ : (TopCat.toSSet.obj (TopCat.of ↥A)) ⟶ (TopCat.toSSet.obj X) :=
    TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)
  -- the naturality square of the base change, in the form proved by area SERRE
  have hsq : (Work.Serre.Phi (TopCat.toSSet.obj (TopCat.of ↥A))).hom ≫ Work.Serre.cmQ σ
      = (Work.Serre.IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map (Work.Serre.cmZ σ)
        ≫ (Work.Serre.Phi (TopCat.toSSet.obj X)).hom :=
    Work.Serre.Phi_naturality σ
  -- `F` is right exact, so it carries the cokernel to the cokernel
  let e : (Work.Serre.IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (cokernel (Work.Serre.cmZ σ)) ≅ cokernel (Work.Serre.cmQ σ) :=
    Limits.PreservesCokernel.iso (Work.Serre.IntRat.mapHomologicalComplex (ComplexShape.down ℕ))
        (Work.Serre.cmZ σ) ≪≫
      Limits.cokernel.mapIso
        (f := (Work.Serre.IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (Work.Serre.cmZ σ))
        (f' := Work.Serre.cmQ σ)
        (p := Work.Serre.Phi (TopCat.toSSet.obj (TopCat.of ↥A)))
        (q := Work.Serre.Phi (TopCat.toSSet.obj X)) hsq.symm
  -- transport the vanishing along `e`
  have hZ : IsZero ((cokernel (Work.Serre.cmZ σ)).homology n) := h
  have hFZ : IsZero (((Work.Serre.IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (cokernel (Work.Serre.cmZ σ))).homology n) :=
    IsZero.of_iso (Functor.map_isZero Work.Serre.IntRat hZ)
      (Work.StemsB.SphRat.homologyMapBaseChange Work.Serre.IntRat
        (cokernel (Work.Serre.cmZ σ)) n).some
  exact IsZero.of_iso hFZ (HomologicalComplex.homologyMapIso e n).symm

end

end Work.Stems.Engine
