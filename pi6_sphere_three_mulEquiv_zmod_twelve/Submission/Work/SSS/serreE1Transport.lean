import Mathlib
import Submission.Work.Serre.E2dFibre
import Submission.Work.Serre.nonempty_homology_iso_of_isZero_relChains
import Submission.Work.StemsB.FibreTransport
import Submission.Work.Cohomology.Chains
import Submission.Work.PiS.Interfaces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The canonical fibre transport of a Serre fibration along a path

This file constructs, for a Serre fibration `p : E → B` and a path `γ` in `B`, the *canonical*
isomorphism `HZ (p⁻¹γ(0)) ≅ HZ (p⁻¹γ(1))` on integral singular homology, namely the one induced by
the fibre inclusions of the pullback `q = pullbackSnd p γ : ↥(Pullback p γ) → I`: since the pair
`(↥(Pullback p γ), q⁻¹{t})` has vanishing relative homology for `t = 0, 1` (the interval is
contractible), the inclusions `inclChains` induce isomorphisms on homology
(`Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains`), and the transport is their
composite, transported along the canonical homeomorphism `q⁻¹{t} ≅ p⁻¹(γ t)`
(`Work.SSS.pullbackFibreHomeo`).

The point of having the *construction* (and not merely its existence,
`Work.SSS.fibreTransportAPI`) is that the coherence clauses

* `Work.SSS.transportIsoPath_trans` — invariance under concatenation of paths,
* `Work.SSS.transportIsoPath_homotopic` — invariance under homotopies of paths rel endpoints,
* `Work.SSS.transportIsoPath_refl` — triviality on constant paths,

are statements about this specific construction; together with
`Work.SSS.fibreTrivializationOfSimplyConn` they trivialise the local system `b ↦ HZ (p⁻¹b)` of the
E¹ page of the Serre spectral sequence over a simply connected base.
-/

set_option autoImplicit false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.SSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- Homology is invariant under a homeomorphism of spaces. -/
def HZHomeoIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (j : ℕ) :
    (Work.PiS.HZ X j) ≅ (Work.PiS.HZ Y j) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) j).mapIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo e))

/-- **The fibre of the pullback of `p` along a path `δ` over `t` is the fibre of `p` over `δ t`.**
The analogue, for the interval, of `Work.Serre.pbFibreHomeo` (which is stated for cubes). -/
def pullbackFibreHomeo (p : C(E, B)) (δ : C(unitInterval, B)) (t : unitInterval) :
    ↥{x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = t} ≃ₜ
      Work.StemsB.fibre p (δ t) where
  toFun y := ⟨(y.1 : Work.StemsB.Pullback p δ).1.1, by
    have h1 : p ((y.1 : Work.StemsB.Pullback p δ).1.1)
        = δ ((y.1 : Work.StemsB.Pullback p δ).1.2) := (y.1 : Work.StemsB.Pullback p δ).2
    have h2 : (y.1 : Work.StemsB.Pullback p δ).1.2 = t := y.2
    rw [h2] at h1
    exact h1⟩
  invFun e := ⟨⟨(e.1, t), e.2⟩, rfl⟩
  left_inv y := by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    exact (y.2).symm
  right_inv e := by
    refine Subtype.ext rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    fun_prop

/-- **The canonical transport of fibre homology along a path**, in the shape of the *pullback*: the
composite of the homology isomorphisms induced by the two fibre inclusions of the pullback of `p`
along `δ`. -/
def pullbackTransportIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (δ : C(unitInterval, B)) (j : ℕ) :
    (Work.PiS.HZ ↥{x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = 0} j) ≅
      (Work.PiS.HZ ↥{x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = 1} j) := by
  have hq : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd p δ) :=
    fun i => Work.StemsB.hasHLP_pullback p δ (hp i)
  haveI h0 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains
      (TopCat.of (Work.StemsB.Pullback p δ))
      {x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = 0}) j) :=
    Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
      (fun m => Work.Serre.isZero_relChains_fibre_of_contraction
        (Work.StemsB.pullbackSnd p δ) hq 0 Work.StemsB.unitContrZero
        Work.StemsB.unitContrZero_zero Work.StemsB.unitContrZero_one
        Work.StemsB.unitContrZero_fixes m) j
  haveI h1 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains
      (TopCat.of (Work.StemsB.Pullback p δ))
      {x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = 1}) j) :=
    Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
      (fun m => Work.Serre.isZero_relChains_fibre_of_contraction
        (Work.StemsB.pullbackSnd p δ) hq 1 Work.StemsB.unitContrOne
        Work.StemsB.unitContrOne_zero Work.StemsB.unitContrOne_one
        Work.StemsB.unitContrOne_fixes m) j
  exact (asIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains
      (TopCat.of (Work.StemsB.Pullback p δ))
      {x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = 0}) j)) ≪≫
    (asIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains
      (TopCat.of (Work.StemsB.Pullback p δ))
      {x : Work.StemsB.Pullback p δ | Work.StemsB.pullbackSnd p δ x = 1}) j)).symm

/-- **The canonical fibre transport of a Serre fibration along a path.**  The transport iso for a
path, expressed between the fibres over the *declared* endpoints of the path (so that the coherence
clauses below are clean statements about `Path.trans` and `Path.Homotopic`). -/
def transportIsoPath (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (j : ℕ) :
    (Work.PiS.HZ (Work.StemsB.fibre p b₀) j) ≅ (Work.PiS.HZ (Work.StemsB.fibre p b₁) j) :=
  (eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) γ.source'.symm)) ≪≫
  (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 0) j).symm ≪≫
  pullbackTransportIso p hp γ.toContinuousMap j ≪≫
  (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) j) ≪≫
  (eqToIso (congrArg (fun x => Work.PiS.HZ (Work.StemsB.fibre p x) j) γ.target'))

end

end Work.SSS
