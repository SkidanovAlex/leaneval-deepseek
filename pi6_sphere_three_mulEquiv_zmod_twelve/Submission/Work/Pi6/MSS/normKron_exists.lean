import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.MSS.kunnethDefs
import Submission.Work.Pi6.MSS.fieldDualUCT_explicit
import Submission.Work.Cohomology.cupH
import Submission.Work.Cohomology.kronH_natural
import Submission.Work.Cohomology.homotopyEquivDual
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The explicit Kronecker pairing against the normalized chain complex

`Work.Pi6.MSS.normKron_exists` is the explicit form of the field universal coefficient theorem for
the *normalized* chain complex `N_*(B;𝕜)` of a space `B`: there is a linear equivalence
`H^s(B;𝕜) ≃ₗ Hom_𝕜(H_s(N_*(B;𝕜)), 𝕜)` whose value on the class of a cocycle `α` and the class of a
cycle `z` of the normalized complex is `α` evaluated on `z`, transported into the unnormalized
chain complex by the chain map `fromNormalizedChainComplex`.

The proof composes

* the field universal coefficient pairing `Work.Pi6.MSS.fieldDualUCT_explicit` on the normalized
  complex (whose value rule on classes is `Work.Pi6.SQM.SIG.sigKron_spec`), and
* the inverse of the homology isomorphism induced by `fromNormalizedChainComplex`, obtained from
  `SSet.homotopyEquivNormalizedChainComplex` (the same source as `Work.Pi6.MSS.normCoh`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

/-- The homology isomorphism induced by `X.fromNormalizedChainComplex R` (the splitting of the
normalized chain complex into the unnormalized one), as a linear equivalence. -/
def fromNormHomologyEquiv (𝕜 : Type) [Field 𝕜] (X : SSet) (s : ℕ) :
    (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)).homology s ≃ₗ[𝕜]
      (X.chainComplex (ModuleCat.of 𝕜 𝕜)).homology s := by
  classical
  let R : ModuleCat 𝕜 := ModuleCat.of 𝕜 𝕜
  let A : ChainComplex (ModuleCat 𝕜) ℕ := X.normalizedChainComplex R
  let Bc : ChainComplex (ModuleCat 𝕜) ℕ := X.chainComplex R
  have htofrom : X.toNormalizedChainComplex R ≫ X.fromNormalizedChainComplex R
      = (X.homotopyEquivNormalizedChainComplex R).hom ≫
        (X.homotopyEquivNormalizedChainComplex R).inv := rfl
  have hfg : homologyMap (X.toNormalizedChainComplex R) s ≫
      homologyMap (X.fromNormalizedChainComplex R) s = 𝟙 (Bc.homology s) := by
    rw [← homologyMap_comp, htofrom,
      Homotopy.homologyMap_eq (X.homotopyEquivNormalizedChainComplex R).homotopyHomInvId s]
    exact homologyMap_id Bc s
  have hgf : homologyMap (X.fromNormalizedChainComplex R) s ≫
      homologyMap (X.toNormalizedChainComplex R) s = 𝟙 (A.homology s) := by
    rw [← homologyMap_comp, SSet.fromNormalizedChainComplex_toNormalizedChainComplex]
    exact homologyMap_id A s
  have e1 : ∀ x : A.homology s,
      (homologyMap (X.toNormalizedChainComplex R) s).hom
        ((homologyMap (X.fromNormalizedChainComplex R) s).hom x) = x := by
    intro x
    have h := congrArg (fun (m : A.homology s ⟶ A.homology s) => m.hom x) hgf
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h
  have e2 : ∀ y : Bc.homology s,
      (homologyMap (X.fromNormalizedChainComplex R) s).hom
        ((homologyMap (X.toNormalizedChainComplex R) s).hom y) = y := by
    intro y
    have h := congrArg (fun (m : Bc.homology s ⟶ Bc.homology s) => m.hom y) hfg
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h
  exact
    { toFun := (homologyMap (X.fromNormalizedChainComplex R) s).hom
      invFun := (homologyMap (X.toNormalizedChainComplex R) s).hom
      left_inv := e1
      right_inv := e2
      map_add' := (homologyMap (X.fromNormalizedChainComplex R) s).hom.map_add
      map_smul' := (homologyMap (X.fromNormalizedChainComplex R) s).hom.map_smul }

@[simp]
theorem fromNormHomologyEquiv_apply (𝕜 : Type) [Field 𝕜] (X : SSet) (s : ℕ)
    (x : (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)).homology s) :
    fromNormHomologyEquiv 𝕜 X s x =
      (homologyMap (X.fromNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)) s).hom x := rfl

theorem normKron_exists (𝕜 : Type) [Field 𝕜] (B : Type) [TopologicalSpace B] (s : ℕ) :
    ∃ e : Work.Pi6.Coh 𝕜 B s ≃ₗ[𝕜] (↥((Work.Pi6.MSS.normC 𝕜 B).homology s) →ₗ[𝕜] 𝕜),
      (∀ (α : Work.Cohomology.Cochain 𝕜 (TopCat.toSSet.obj (TopCat.of B)) s)
         (hα : Work.Cohomology.cochainDiff 𝕜 (TopCat.toSSet.obj (TopCat.of B)) α = 0)
         (z : (Work.Pi6.MSS.normC 𝕜 B).cycles s),
        e (Work.Cohomology.cohomologyClassOf 𝕜 (TopCat.toSSet.obj (TopCat.of B)) α hα)
          (((Work.Pi6.MSS.normC 𝕜 B).homologyπ s) z)
        = α (((SSet.fromNormalizedChainComplex (TopCat.toSSet.obj (TopCat.of B))
              (ModuleCat.of 𝕜 𝕜)).f s).hom
              ((ModuleCat.Hom.hom ((Work.Pi6.MSS.normC 𝕜 B).iCycles s)) z))) := by
  classical
  let X : SSet := TopCat.toSSet.obj (TopCat.of B)
  change ∃ e : ↥((Work.Cohomology.cochainC 𝕜 X).homology s) ≃ₗ[𝕜]
      (↥((X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)).homology s) →ₗ[𝕜] 𝕜),
    ∀ (α : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X s →ₗ[𝕜] 𝕜)
      (hα : Work.Cohomology.cochainDiff 𝕜 X α = 0)
      (z : (X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)).cycles s),
      e (Work.Cohomology.cohomologyClassOf 𝕜 X α hα)
        (((X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)).homologyπ s) z)
      = α (((SSet.fromNormalizedChainComplex X (ModuleCat.of 𝕜 𝕜)).f s).hom
            ((ModuleCat.Hom.hom ((X.normalizedChainComplex (ModuleCat.of 𝕜 𝕜)).iCycles s)) z))
  refine ⟨(LinearEquiv.ofBijective (Work.Cohomology.kronH 𝕜 X s)
      (Work.Cohomology.kronH_bijective_field 𝕜 X s)).trans
      (LinearEquiv.dualMap (fromNormHomologyEquiv 𝕜 X s)), ?_⟩
  intro α hα z
  rw [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, LinearEquiv.ofBijective_apply]
  rw [fromNormHomologyEquiv_apply]
  rw [Work.Cohomology.homologyMap_homologyπ_apply
    (X.fromNormalizedChainComplex (ModuleCat.of 𝕜 𝕜)) s z]
  rw [Work.Cohomology.kronH_apply 𝕜 X α hα]
  rw [Work.Pi6.SQM.SIG.cyclesMap_i_apply]

end

end Work.Pi6.MSS
