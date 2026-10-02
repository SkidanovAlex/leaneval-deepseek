import Mathlib
import Submission.Work.Thom.tsqHonest
import Submission.Work.Thom.tsqInfra
import Submission.Work.Thom.MixedCup
import Submission.Work.Thom.mixedCupC_pairNatural
import Submission.Work.Thom.exists_snake_data
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Thom.transgressionBasic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Thom

noncomputable section

/-! ## 1. The cup product with a relative cocycle, as a map of cochain complexes -/

/-- The cup product with a fixed relative cochain, as a linear map on the cochains of any relative
complex over the same space. -/
noncomputable def cupRightLM {Y : TopCat} {B : Set Y} {n : ℕ}
    (t : ↥((Work.Cohomology.relComplex ℤ Y B).X n)) (B' : Set Y) (p : ℕ) :
    ↥((Work.Cohomology.relComplex ℤ Y B').X p) →ₗ[ℤ]
      ↥((Work.Cohomology.relComplex ℤ Y B).X (p + n)) :=
  { toFun := fun c =>
      ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj Y) c.1 t.1,
        Work.Cohomology.cup_mem_relKern_right ℤ Y B c.1 t.2⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      simp only [Submodule.coe_add]
      exact (Work.Cohomology.cupBilinear ℤ (TopCat.toSSet.obj Y) p n).1 a.1 b.1 t.1
    map_smul' := by
      intro a b
      apply Subtype.ext
      simp only [Submodule.coe_smul]
      exact (Work.Cohomology.cupBilinear ℤ (TopCat.toSSet.obj Y) p n).2.1 a b.1 t.1 }

@[simp]
theorem cupRightLM_apply {Y : TopCat} {B : Set Y} {n : ℕ}
    (t : ↥((Work.Cohomology.relComplex ℤ Y B).X n)) (B' : Set Y) (p : ℕ)
    (c : ↥((Work.Cohomology.relComplex ℤ Y B').X p)) :
    ((cupRightLM t B' p) c).1 = Work.Cohomology.cup ℤ (TopCat.toSSet.obj Y) c.1 t.1 := rfl

/-- The condition that cup-with-`t` commutes with the consecutive differentials. -/
def CupComm {Y : TopCat} {B : Set Y} {n : ℕ} (t : ↥((Work.Cohomology.relComplex ℤ Y B).X n))
    (B' : Set Y) : Prop :=
  ∀ i : ℕ,
    CategoryTheory.CategoryStruct.comp (ModuleCat.ofHom (cupRightLM t B' i))
        ((Tsq.shK (Work.Cohomology.relComplex ℤ Y B) n).d i (i + 1))
      = CategoryTheory.CategoryStruct.comp ((Work.Cohomology.relComplex ℤ Y B').d i (i + 1))
        (ModuleCat.ofHom (cupRightLM t B' (i + 1)))

/-- **The cup product with a relative cocycle is a morphism of cochain complexes** of degree `n`. -/
noncomputable def cupRightComplex {Y : TopCat} {B : Set Y} {n : ℕ}
    (t : ↥((Work.Cohomology.relComplex ℤ Y B).X n)) (B' : Set Y) (hcomm : CupComm t B') :
    Work.Cohomology.relComplex ℤ Y B' ⟶
      Tsq.shK (Work.Cohomology.relComplex ℤ Y B) n :=
  HomologicalComplex.Hom.mk (fun p => ModuleCat.ofHom (cupRightLM t B' p)) (by
    intro i j hij
    rw [ComplexShape.up_Rel] at hij
    subst hij
    exact hcomm i)

/-- The restriction of a relative cochain of `(X,A)` to a subspace `W`, as a relative cochain of
`(W, A ∩ W)`. -/
noncomputable def relRestrCochain {X : TopCat} (A : Set X) (W : Set X) (n : ℕ) :
    ↥((Work.Cohomology.relComplex ℤ X A).X n) →ₗ[ℤ]
      ↥((Work.Cohomology.relComplex ℤ (TopCat.of ↥W)
        (Work.Cohomology.interAU A W)).X n) :=
  ((Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of ↥W) (X₂ := X)
      (Work.Cohomology.interAU A W) A (Work.Cohomology.subtypeIncl X W)
      (Work.Cohomology.interAU_incl_subtypeIncl X A W)).f n).hom

/-- A cocycle of `(X,A)` restricts to a cocycle of `(W, A ∩ W)`. -/
theorem relRestrCochain_isCocycle {X : TopCat} (A : Set X) (W : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : (ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℤ X A).d n (n + 1))) t = 0) :
    (ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℤ (TopCat.of ↥W)
      (Work.Cohomology.interAU A W)).d n (n + 1))) (relRestrCochain A W n t) = 0 := by
  have hcomm := congrArg
    (fun (φ : (Work.Cohomology.relComplex ℤ X A).X n ⟶
        (Work.Cohomology.relComplex ℤ (TopCat.of ↥W)
          (Work.Cohomology.interAU A W)).X (n + 1)) => ModuleCat.Hom.hom φ t)
    (HomologicalComplex.Hom.comm (Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of ↥W) (X₂ := X)
      (Work.Cohomology.interAU A W) A (Work.Cohomology.subtypeIncl X W)
      (Work.Cohomology.interAU_incl_subtypeIncl X A W)) n (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, relRestrCochain] at hcomm ⊢
  rw [ht, map_zero] at hcomm
  exact hcomm

/-! ## 2. The comparison maps `cmpU`, `cmpV`, `cmpW` are isomorphisms -/

theorem isIso_cmpU (X : TopCat) (A U V : Set X) : IsIso (Work.Cohomology.cmpU X A U V) := by
  haveI h1 : IsIso (Work.Cohomology.HMV.etaU A U V) := (Work.Cohomology.hmv_isIso_eta X A U V).1
  haveI h2 : IsIso (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relMVUU X A U V)
      (Work.Cohomology.relChains (TopCat.of U) (Work.Cohomology.interAU A U))
      (Work.Cohomology.HMV.etaU A U V)) :=
    Work.Cohomology.isIso_dualComplexMap (Work.Cohomology.HMV.etaU A U V)
  rw [show Work.Cohomology.cmpU X A U V = (Work.Cohomology.relDualIsoComplex (TopCat.of U)
      (Work.Cohomology.interAU A U)).inv ≫ Work.Cohomology.dualComplexMap ℤ
      (Work.Cohomology.relMVUU X A U V) (Work.Cohomology.relChains (TopCat.of U)
      (Work.Cohomology.interAU A U)) (Work.Cohomology.HMV.etaU A U V) from rfl]
  infer_instance

theorem isIso_cmpV (X : TopCat) (A U V : Set X) : IsIso (Work.Cohomology.cmpV X A U V) := by
  haveI h1 : IsIso (Work.Cohomology.HMV.etaV A U V) := (Work.Cohomology.hmv_isIso_eta X A U V).2.1
  haveI h2 : IsIso (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relMVVV X A U V)
      (Work.Cohomology.relChains (TopCat.of V) (Work.Cohomology.interAU A V))
      (Work.Cohomology.HMV.etaV A U V)) :=
    Work.Cohomology.isIso_dualComplexMap (Work.Cohomology.HMV.etaV A U V)
  rw [show Work.Cohomology.cmpV X A U V = (Work.Cohomology.relDualIsoComplex (TopCat.of V)
      (Work.Cohomology.interAU A V)).inv ≫ Work.Cohomology.dualComplexMap ℤ
      (Work.Cohomology.relMVVV X A U V) (Work.Cohomology.relChains (TopCat.of V)
      (Work.Cohomology.interAU A V)) (Work.Cohomology.HMV.etaV A U V) from rfl]
  infer_instance

theorem isIso_cmpW (X : TopCat) (A U V : Set X) : IsIso (Work.Cohomology.cmpW X A U V) := by
  haveI h1 : IsIso (Work.Cohomology.relMVUVPhi X A U V) := (Work.Cohomology.hmv_isIso_eta X A U V).2.2
  haveI h2 : IsIso (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relMVUV X A U V)
      (Work.Cohomology.relChains (TopCat.of ↥(U ∩ V)) (Work.Cohomology.interAU A (U ∩ V)))
      (Work.Cohomology.relMVUVPhi X A U V)) :=
    Work.Cohomology.isIso_dualComplexMap (Work.Cohomology.relMVUVPhi X A U V)
  rw [show Work.Cohomology.cmpW X A U V = (Work.Cohomology.relDualIsoComplex (TopCat.of ↥(U ∩ V))
      (Work.Cohomology.interAU A (U ∩ V))).inv ≫ Work.Cohomology.dualComplexMap ℤ
      (Work.Cohomology.relMVUV X A U V) (Work.Cohomology.relChains (TopCat.of ↥(U ∩ V))
      (Work.Cohomology.interAU A (U ∩ V))) (Work.Cohomology.relMVUVPhi X A U V) from rfl]
  infer_instance

/-! ## 3. The three comparison squares of the cup with a relative cocycle -/

/-- The `U`-piece of the transgression morphism. -/
noncomputable def sigmaU (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (hcomm : CupComm (relRestrCochain A U n t) (Work.Cohomology.interAU ∅ U)) :
    Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X ∅ U V) ⟶
      Tsq.shK (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X A U V)) n :=
  (@asIso _ _ _ _ (Work.Cohomology.cmpU X ∅ U V) (isIso_cmpU X ∅ U V)).inv
    ≫ cupRightComplex (relRestrCochain A U n t) (Work.Cohomology.interAU ∅ U) hcomm
    ≫ Tsq.shMap (Work.Cohomology.cmpU X A U V) n

/-- The `V`-piece of the transgression morphism. -/
noncomputable def sigmaV (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (hcomm : CupComm (relRestrCochain A V n t) (Work.Cohomology.interAU ∅ V)) :
    Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X ∅ U V) ⟶
      Tsq.shK (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X A U V)) n :=
  (@asIso _ _ _ _ (Work.Cohomology.cmpV X ∅ U V) (isIso_cmpV X ∅ U V)).inv
    ≫ cupRightComplex (relRestrCochain A V n t) (Work.Cohomology.interAU ∅ V) hcomm
    ≫ Tsq.shMap (Work.Cohomology.cmpV X A U V) n

/-- The overlap component of the transgression morphism. -/
noncomputable def tau3 (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (hcomm : CupComm (relRestrCochain A (U ∩ V) n t) (Work.Cohomology.interAU ∅ (U ∩ V))) :
    Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X ∅ U V) ⟶
      Tsq.shK (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUV X A U V)) n :=
  (@asIso _ _ _ _ (Work.Cohomology.cmpW X ∅ U V) (isIso_cmpW X ∅ U V)).inv
    ≫ cupRightComplex (relRestrCochain A (U ∩ V) n t)
        (Work.Cohomology.interAU ∅ (U ∩ V)) hcomm
    ≫ Tsq.shMap (Work.Cohomology.cmpW X A U V) n

/-! ## 4. The top component: the descent of the cup to the relative small cochains -/

/-- The `p`-th component of the top component of the transgression morphism. -/
noncomputable def tau1LM (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n)) :
    (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V)).X p ⟶
      (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)).X (p + n) :=
  (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.smallChains U V)
      (Work.Cohomology.relMVTopC X ∅ U V)
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.smallInToSmall U V ∅))).f p
    ≫ Work.Thom.cupDescend X A U V n p t.1 t.2

end

end Work.Thom
