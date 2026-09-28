import Submission.Work.StemsB.CollarRat
import Submission.Work.StemsB.WangSphereHomology
import Submission.Work.StemsB.WangSequenceShiftedR
import Submission.Work.StemsB.WangCohSphereShifted

/-!
# The Wang sequence over a sphere, in cohomology, over `ℚ`

The `ℤ`-coefficient Wang sequence over a sphere is a theorem of this directory
(`Work.StemsB.wangCohShiftExactSphere₁/₂/₃`, `Work.StemsB.wangSphereE4`).  Subproject SERRE's engine
is rational, so it needs the same sequence over `ℚ`.  Rather than re-running the whole geometric
chapter over `ℚ`, this file obtains the two identifications `γ` and `τ` of the rational Wang
sequence from the *integral homology* versions (`Work.StemsB.wangGammaSphereHom`,
`Work.StemsB.wangTauSphere`) by the change of rings `- ⊗[ℤ] ℚ` together with field duality:

`H^n(X;ℚ) ≅ Hom_ℚ(H_n(X;ℚ),ℚ) ≅ Hom_ℚ(ℚ ⊗[ℤ] H_n(X;ℤ), ℚ)`,

the second step being the flat base change `H_n(X;ℚ) ≅ H_n(X;ℤ) ⊗[ℤ] ℚ`
(`Work.StemsB.RatBC.Phi`).  An isomorphism of integral homology modules therefore induces one on the
rational cohomology with no further input, and the two *relative* versions
(`Work.StemsB.relChainsBaseChangeRat`, `Work.StemsB.relCohomology_dual_rat`) do the same for the
pair `(E, E|_O)`.

What this gives is the **exactness** half of the rational Wang sequence E4 in every degree.  The
multiplicative *derivation property* of the transgression θ is a statement about the cup product and
is not obtained this way; it is the subject of the separate rational collar chapter.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Work.StemsB

noncomputable section

open Work.Cohomology

/-! ## Rational cohomology as the dual of the base change of integral homology -/

/-- The base change `H_n(X;ℚ) ≅ ℚ ⊗[ℤ] H_n(X;ℤ)` of the homology of a space. -/
noncomputable def homologyBaseChangeRat (X : TopCat) (n : ℕ) :
    (singularChains ℚ X).homology n ≅ IntRatF.obj ((singularChains ℤ X).homology n) := by
  haveI : PreservesFiniteLimits IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits IntRatF := inferInstance
  haveI : IntRatF.PreservesHomology := inferInstance
  exact (HomologicalComplex.homologyMapIso (RatBC.Phi (TopCat.toSSet.obj X)) n).symm ≪≫
    (SphRat.homologyMapBaseChange IntRatF (singularChains ℤ X) n).some

/-- **Rational cohomology as the `ℚ`-dual of the base change of integral homology.** -/
noncomputable def ratCohTensorDual (X : TopCat) (n : ℕ) :
    Work.Cohomology.singularCohomology ℚ n X ≅
      ModuleCat.of ℚ (↥(IntRatF.obj ((singularChains ℤ X).homology n)) →ₗ[ℚ] ℚ) :=
  (fieldDualUCT ℚ (singularChains ℚ X) n).some ≪≫
    LinearEquiv.toModuleIso
      (LinearEquiv.dualMap (homologyBaseChangeRat X n).toLinearEquiv.symm)

/-- An isomorphism of integral homology modules induces one on the `ℚ`-duals of their base
changes. -/
noncomputable def tensorDualMapIso {M N : ModuleCat.{0} ℤ} (e : M ≅ N) :
    ModuleCat.of ℚ (↥(IntRatF.obj N) →ₗ[ℚ] ℚ) ≅
      ModuleCat.of ℚ (↥(IntRatF.obj M) →ₗ[ℚ] ℚ) :=
  LinearEquiv.toModuleIso (LinearEquiv.dualMap (IntRatF.mapIso e).toLinearEquiv)

/-! ## The relative version -/

/-- The base change of the *relative* homology, `H_n(X,A;ℚ) ≅ ℚ ⊗[ℤ] H_n(X,A;ℤ)`. -/
noncomputable def relHomologyBaseChangeRat (X : TopCat) (A : Set X) (n : ℕ) :
    (relChainsR ℚ X A).homology n ≅ IntRatF.obj ((relChains X A).homology n) := by
  haveI : PreservesFiniteLimits IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits IntRatF := inferInstance
  haveI : IntRatF.PreservesHomology := inferInstance
  exact (HomologicalComplex.homologyMapIso (relChainsBaseChangeRat X A).some n).symm ≪≫
    (SphRat.homologyMapBaseChange IntRatF (relChains X A) n).some

/-- **Rational relative cohomology as the `ℚ`-dual of the base change of integral relative
homology.** -/
noncomputable def ratRelCohTensorDual (X : TopCat) (A : Set X) (n : ℕ) :
    (relComplex ℚ X A).homology n ≅
      ModuleCat.of ℚ (↥(IntRatF.obj ((relChains X A).homology n)) →ₗ[ℚ] ℚ) := by
  exact (relCohomology_dual_rat X A n).some ≪≫ LinearEquiv.toModuleIso
    (LinearEquiv.dualMap (relHomologyBaseChangeRat X A n).toLinearEquiv.symm)

/-! ## The two identifications of the rational Wang sequence over a sphere -/

/-- The fibre of the rational Wang sequence over the sphere. -/
abbrev wangCohFsp' (b : ℕ) {E : Type} [TopologicalSpace E] (p : C(E, SphModel b)) : TopCat :=
  TopCat.of ↥(p ⁻¹' {OnePoint.infty})

/-- **The identification `γ` of the rational Wang sequence over a sphere**, obtained from the
integral homology one by base change and duality. -/
noncomputable def wangGammaSphereOuterRat (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    ∀ k : ℕ, Work.Cohomology.singularCohomology ℚ k (TopCat.of (p ⁻¹' sphLoopOuter b)) ≅
      Work.Cohomology.singularCohomology ℚ k (wangCohFsp' b p) := fun k =>
  ratCohTensorDual (TopCat.of (p ⁻¹' sphLoopOuter b)) k ≪≫
    tensorDualMapIso (wangGammaSphereHom b hb E p hT_O k).symm ≪≫
    (ratCohTensorDual (wangCohFsp' b p) k).symm

/-- **The identification `τ` of the rational Wang sequence over a sphere.** -/
noncomputable def wangTauSphereRat (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    ∀ n : ℕ, (relComplex ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b)).homology (n + b) ≅
      Work.Cohomology.singularCohomology ℚ n (wangCohFsp' b p) := fun n => by
  have hcast : ((n + b : ℕ) : ℤ) - (b : ℤ) = ((n : ℕ) : ℤ) := by
    push_cast
    omega
  have hτ : (relChains (TopCat.of E) (p ⁻¹' sphLoopOuter b)).homology (n + b) ≅
      (singularChains ℤ (TopCat.of ↥(p ⁻¹' {OnePoint.infty}))).homology n :=
    wangTauSphere b hb E p hp d_G hT_G (n + b) ≪≫
      eqToIso (congrArg (chainZ (TopCat.of ↥(p ⁻¹' {OnePoint.infty}))) hcast)
  exact ratRelCohTensorDual (TopCat.of E) (p ⁻¹' sphLoopOuter b) (n + b) ≪≫
    tensorDualMapIso hτ.symm ≪≫
    (ratCohTensorDual (wangCohFsp' b p) n).symm

/-- **The identification `τS` of the rational Wang sequence over a sphere**, at the shifted degree
`n + b + 1`. -/
noncomputable def wangTauSphereRatS (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    ∀ n : ℕ, (relComplex ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b)).homology (n + b + 1) ≅
      Work.Cohomology.singularCohomology ℚ (n + 1) (wangCohFsp' b p) := fun n =>
  eqToIso (congrArg (fun t => (relComplex ℚ (TopCat.of E)
      (p ⁻¹' sphLoopOuter b)).homology t) (show n + b + 1 = (n + 1) + b by omega)) ≪≫
    wangTauSphereRat b hb E p hp d_G hT_G (n + 1)

/-! ## Exactness of the rational Wang sequence over a sphere -/

/-- **Exactness of the rational Wang sequence over a sphere at `H^{n+b}(E;ℚ)`.** -/
theorem wangCohShiftExactSphereRat₁ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (wangCohShiftβR ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp' b p) b
        (wangTauSphereRat b hb E p hp d_G hT_G) n)
      (wangCohShiftαR ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp' b p) b
        (wangGammaSphereOuterRat b hb E p hT_O) (n + b)) :=
  wangCohShiftExact₁R ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp' b p) b
    (wangGammaSphereOuterRat b hb E p hT_O) (wangTauSphereRat b hb E p hp d_G hT_G) n

/-- **Exactness of the rational Wang sequence over a sphere at `H^{n+b}(F;ℚ)`.** -/
theorem wangCohShiftExactSphereRat₂ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (wangCohShiftαR ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp' b p) b
        (wangGammaSphereOuterRat b hb E p hT_O) (n + b))
      (wangCohShiftθR ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp' b p) b
        (wangGammaSphereOuterRat b hb E p hT_O)
        (wangTauSphereRatS b hb E p hp d_G hT_G) n) :=
  wangCohShiftExact₂R ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp' b p) b
    (wangGammaSphereOuterRat b hb E p hT_O) (wangTauSphereRatS b hb E p hp d_G hT_G) n

/-- **Exactness of the rational Wang sequence over a sphere at `H^{n+b+1}(E, E|_O;ℚ)`.** -/
theorem wangCohShiftExactSphereRat₃ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (wangCohShiftθR ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp' b p) b
        (wangGammaSphereOuterRat b hb E p hT_O)
        (wangTauSphereRatS b hb E p hp d_G hT_G) n)
      (wangCohShiftβSR ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp' b p) b
        (wangTauSphereRatS b hb E p hp d_G hT_G) n) :=
  wangCohShiftExact₃R ℚ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp' b p) b
    (wangGammaSphereOuterRat b hb E p hT_O) (wangTauSphereRatS b hb E p hp d_G hT_G) n

end

end Work.StemsB
