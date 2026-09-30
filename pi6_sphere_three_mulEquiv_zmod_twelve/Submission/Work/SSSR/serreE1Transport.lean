import Mathlib
import Submission.Work.SSSR.Serre.E2dFibre
import Submission.Work.SSSR.Serre.nonempty_homology_iso_of_isZero_relChains
import Submission.Work.SSSR.StemsB.FibreTransport
import Submission.Work.SSSR.Cohomology.Chains
import Submission.Work.SSSR.PiS.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits
namespace Work.SSSR

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- Homology is invariant under a homeomorphism of spaces. -/
def HZHomeoIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (j : ℕ) :
    (Work.SSSR.PiS.HZ R X j) ≅ (Work.SSSR.PiS.HZ R Y j) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) j).mapIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj
      (ModuleCat.of R R)).mapIso (TopCat.isoOfHomeo e))

/-- **The fibre of the pullback of `p` along a path `δ` over `t` is the fibre of `p` over `δ t`.**
The analogue, for the interval, of `Work.Serre.pbFibreHomeo` (which is stated for cubes). -/
def pullbackFibreHomeo (p : C(E, B)) (δ : C(unitInterval, B)) (t : unitInterval) :
    ↥{x : Work.SSSR.StemsB.Pullback p δ | Work.SSSR.StemsB.pullbackSnd p δ x = t} ≃ₜ
      Work.SSSR.StemsB.fibre p (δ t) where
  toFun y := ⟨(y.1 : Work.SSSR.StemsB.Pullback p δ).1.1, by
    have h1 : p ((y.1 : Work.SSSR.StemsB.Pullback p δ).1.1)
        = δ ((y.1 : Work.SSSR.StemsB.Pullback p δ).1.2) := (y.1 : Work.SSSR.StemsB.Pullback p δ).2
    have h2 : (y.1 : Work.SSSR.StemsB.Pullback p δ).1.2 = t := y.2
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
def pullbackTransportIso (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p)
    (δ : C(unitInterval, B)) (j : ℕ) :
    (Work.SSSR.PiS.HZ R ↥{x : Work.SSSR.StemsB.Pullback p δ | Work.SSSR.StemsB.pullbackSnd p δ x = 0} j) ≅
      (Work.SSSR.PiS.HZ R ↥{x : Work.SSSR.StemsB.Pullback p δ | Work.SSSR.StemsB.pullbackSnd p δ x = 1} j) := by
  have hq : Work.SSSR.StemsB.IsSerreFibration (Work.SSSR.StemsB.pullbackSnd p δ) :=
    fun i => Work.SSSR.StemsB.hasHLP_pullback p δ (hp i)
  haveI h0 : IsIso (HomologicalComplex.homologyMap (Work.SSSR.Cohomology.inclChains R
      (TopCat.of (Work.SSSR.StemsB.Pullback p δ))
      {x : Work.SSSR.StemsB.Pullback p δ | Work.SSSR.StemsB.pullbackSnd p δ x = 0}) j) :=
    Work.SSSR.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
      (fun m => Work.SSSR.Serre.isZero_relChains_fibre_of_contraction
        (Work.SSSR.StemsB.pullbackSnd p δ) hq 0 Work.SSSR.StemsB.unitContrZero
        Work.SSSR.StemsB.unitContrZero_zero Work.SSSR.StemsB.unitContrZero_one
        Work.SSSR.StemsB.unitContrZero_fixes m) j
  haveI h1 : IsIso (HomologicalComplex.homologyMap (Work.SSSR.Cohomology.inclChains R
      (TopCat.of (Work.SSSR.StemsB.Pullback p δ))
      {x : Work.SSSR.StemsB.Pullback p δ | Work.SSSR.StemsB.pullbackSnd p δ x = 1}) j) :=
    Work.SSSR.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
      (fun m => Work.SSSR.Serre.isZero_relChains_fibre_of_contraction
        (Work.SSSR.StemsB.pullbackSnd p δ) hq 1 Work.SSSR.StemsB.unitContrOne
        Work.SSSR.StemsB.unitContrOne_zero Work.SSSR.StemsB.unitContrOne_one
        Work.SSSR.StemsB.unitContrOne_fixes m) j
  exact (asIso (HomologicalComplex.homologyMap (Work.SSSR.Cohomology.inclChains R
      (TopCat.of (Work.SSSR.StemsB.Pullback p δ))
      {x : Work.SSSR.StemsB.Pullback p δ | Work.SSSR.StemsB.pullbackSnd p δ x = 0}) j)) ≪≫
    (asIso (HomologicalComplex.homologyMap (Work.SSSR.Cohomology.inclChains R
      (TopCat.of (Work.SSSR.StemsB.Pullback p δ))
      {x : Work.SSSR.StemsB.Pullback p δ | Work.SSSR.StemsB.pullbackSnd p δ x = 1}) j)).symm

/-- **The canonical fibre transport of a Serre fibration along a path.**  The transport iso for a
path, expressed between the fibres over the *declared* endpoints of the path (so that the coherence
clauses below are clean statements about `Path.trans` and `Path.Homotopic`). -/
def transportIsoPath (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (j : ℕ) :
    (Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b₀) j) ≅ (Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b₁) j) :=
  (eqToIso (congrArg (fun x => Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p x) j) γ.source'.symm)) ≪≫
  (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 0) j).symm ≪≫
  pullbackTransportIso p hp γ.toContinuousMap j ≪≫
  (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) j) ≪≫
  (eqToIso (congrArg (fun x => Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p x) j) γ.target'))

end

end Work.SSSR
