import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.diskPairHomologyZero
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.gradedComm
import Submission.Work.Crux33.CupAux
import Submission.Work.Cohomology.CompatTrans.Crux33.scEZTools

set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary material for the chain-level Künneth evaluation on `S³ × S³`

This file collects, for the target `Work.Cohomology.Crux33.sph3DiscCupEval`, the material that is
*not* already in the workspace:

* the pairing simplicial map `scZip` from the levelwise product of the singular simplicial sets of
  the two sphere factors to the singular simplicial set of `A = S³ × S³ = PairAT`, with its two
  projection identities (`scZipMap`);
* freeness of the singular homology of the two spheres (`scFreeHomologySph3T`,
  `scFreeHomologySphIn`), hence the Kronecker-pairing device `scDetectedPair`: a `3`-cocycle
  and a `3`-cycle with nonzero evaluation;
* the chain-level agreement of `PInfty` with the identity on cycles (`scPInf_apply_chain_eq`) and
  the resulting *normalized* detecting pair (`scExistsNormalizedDetected`);
* the junk-killing step `scKills_of_normalized` turning "vanishes on degenerate simplices" into the
  hypothesis of the shuffle evaluation;
* the graded-commutativity bookkeeping `scCupSwapEval` for the cup-1 identity.

The final witnesses are assembled as `scKunnethWitness` (the good order for the shuffle
evaluation) and `scTargetWitness` (the order appearing in the statement of `sph3DiscCupEval`).
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Cohomology.Crux33

noncomputable section

/-- The singular simplicial set of `Sph3T`. -/
abbrev SphX : SSet := TopCat.toSSet.obj Sph3T

/-- The singular simplicial set of the sphere `S³ ⊆ D⁴`. -/
abbrev SphY : SSet := TopCat.toSSet.obj (TopCat.of (sphereInUnit 4))

/-- The singular simplicial set of `A = PairAT = S³ × S³`. -/
abbrev SphA : SSet := TopCat.toSSet.obj (TopCat.of PairAT)

/-! ## 1. The pairing map `toSSet S³ ⊗ toSSet S³' ⟶ toSSet A` -/

/-- The value of the singular-simplex equivalence on the map `toSSet.map g`: postcomposition. -/
lemma scToSSetObjEquiv_map_apply (P P' : TopCat) (g : P ⟶ P') (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj P).obj n) (t : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    ((TopCat.toSSetObjEquivT P' n) ((ConcreteCategory.hom ((TopCat.toSSet.map g).app n)) x)) t
      = g (((TopCat.toSSetObjEquivT P n) x) t) := rfl

/-- The levelwise pairing of singular simplices. -/
def scZipAux (P Q : TopCat) (n : SimplexCategoryᵒᵖ)
    (p : (scPairObj (TopCat.toSSet.obj P) (TopCat.toSSet.obj Q)).obj n) :
    (TopCat.toSSet.obj (TopCat.of (↥P × ↥Q))).obj n :=
  (TopCat.toSSetObjEquivT (TopCat.of (↥P × ↥Q)) n).symm
    ⟨fun t => (((TopCat.toSSetObjEquivT P n) p.1) t, ((TopCat.toSSetObjEquivT Q n) p.2) t),
      by fun_prop⟩

/-- The value of the equivalence on `scZipAux`. -/
@[simp] lemma scToSSetObjEquiv_scZipAux (P Q : TopCat) (n : SimplexCategoryᵒᵖ)
    (p : (scPairObj (TopCat.toSSet.obj P) (TopCat.toSSet.obj Q)).obj n)
    (t : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    ((TopCat.toSSetObjEquivT (TopCat.of (↥P × ↥Q)) n) (scZipAux P Q n p)) t
      = (((TopCat.toSSetObjEquivT P n) p.1) t, ((TopCat.toSSetObjEquivT Q n) p.2) t) := by
  rw [scZipAux]
  exact DFunLike.congr_fun (Equiv.apply_symm_apply _ _) t

/-- **The canonical map from the levelwise product of two singular simplicial sets to the singular
simplicial set of the product space.** -/
def scZip (P Q : TopCat) : scPairObj (TopCat.toSSet.obj P) (TopCat.toSSet.obj Q) ⟶
    TopCat.toSSet.obj (TopCat.of (↥P × ↥Q)) where
  app n := TypeCat.ofHom (scZipAux P Q n)
  naturality _ _ f := by
    first
      | rfl
      | (ext p
         apply (TopCat.toSSetObjEquivT _ _).injective
         ext t <;>
         · have key := fun w => TopCat.toSSetObjEquivT_map_apply' (X := TopCat.of (↥P × ↥Q)) f w t
           simp [scZipAux, TopCat.toSSetObjEquivT_map_apply', scPairObj, key])
      | (ext p
         apply (TopCat.toSSetObjEquivT _ _).injective
         ext t <;>
         · have key := fun w => TopCat.toSSetObjEquivT_map_apply' (X := TopCat.of (↥P × ↥Q)) f w t
           simp only [scZipAux, scPairObj, TopCat.toSSetObjEquivT_map_apply']
           rw [key, Equiv.apply_symm_apply]
           rfl)
      | (ext p
         apply (TopCat.toSSetObjEquivT _ _).injective
         ext t <;> simp [scZipAux, TopCat.toSSetObjEquivT_map_apply', scPairObj])
      | (ext p
         apply (TopCat.toSSetObjEquivT _ _).injective
         ext t <;> simp [scZipAux, TopCat.toSSetObjEquivT_map_apply', scPairObj] <;> rfl)
      | (ext p
         apply (TopCat.toSSetObjEquivT _ _).injective
         ext t <;>
         · simp only [scZipAux, scPairObj, TypeCat.hom_comp, Function.comp_apply] at *
           erw [TopCat.toSSetObjEquivT_map_apply', TopCat.toSSetObjEquivT_map_apply',
             Equiv.apply_symm_apply]
           rfl)
      | (ext p
         apply (TopCat.toSSetObjEquivT _ _).injective
         ext t <;>
         · simp [scZipAux, TopCat.toSSetObjEquivT_map_apply', scPairObj]
           erw [TopCat.toSSetObjEquivT_map_apply', Equiv.apply_symm_apply]
           rfl)

/-- The first projection of the product space, as a morphism of `TopCat`. -/
def scFstHom (P Q : TopCat) : TopCat.of (↥P × ↥Q) ⟶ P :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The second projection of the product space, as a morphism of `TopCat`. -/
def scSndHom (P Q : TopCat) : TopCat.of (↥P × ↥Q) ⟶ Q :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

@[simp] lemma scFstHom_apply (P Q : TopCat) (p : ↥P × ↥Q) : scFstHom P Q p = p.1 := rfl
@[simp] lemma scSndHom_apply (P Q : TopCat) (p : ↥P × ↥Q) : scSndHom P Q p = p.2 := rfl

/-- The first projection of `scZip` is the first projection of the levelwise product. -/
lemma scZip_fst (P Q : TopCat) :
    scZip P Q ≫ TopCat.toSSet.map (scFstHom P Q)
      = scPairFst (TopCat.toSSet.obj P) (TopCat.toSSet.obj Q) := by
  ext n p
  apply (TopCat.toSSetObjEquivT P n).injective
  ext t
  show ((TopCat.toSSetObjEquivT P n)
      ((TopCat.toSSet.map (scFstHom P Q)).app n (scZipAux P Q n p))) t = _
  rw [scToSSetObjEquiv_map_apply, scToSSetObjEquiv_scZipAux]
  rfl

/-- The second projection of `scZip` is the second projection of the levelwise product. -/
lemma scZip_snd (P Q : TopCat) :
    scZip P Q ≫ TopCat.toSSet.map (scSndHom P Q)
      = scPairSnd (TopCat.toSSet.obj P) (TopCat.toSSet.obj Q) := by
  ext n p
  apply (TopCat.toSSetObjEquivT Q n).injective
  ext t
  show ((TopCat.toSSetObjEquivT Q n)
      ((TopCat.toSSet.map (scSndHom P Q)).app n (scZipAux P Q n p))) t = _
  rw [scToSSetObjEquiv_map_apply, scToSSetObjEquiv_scZipAux]
  rfl

/-- The identity-like homeomorphism `S³ × S³' ≅ A = PairAT`. -/
def scHomeo : TopCat.of (↥Sph3T × ↥(sphereInUnit 4)) ≅ TopCat.of PairAT :=
  TopCat.isoOfHomeo
    { toFun := fun p ↦ ⟨(p.1, p.2.1), p.2.2⟩
      invFun := fun q ↦ (q.1.1, ⟨q.1.2, q.2⟩)
      left_inv := fun p ↦ by rfl
      right_inv := fun q ↦ by rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

lemma scHomeo_pj1A :
    scHomeo.hom ≫ pj1A = scFstHom Sph3T (TopCat.of (sphereInUnit 4)) := by
  ext p
  rfl

lemma scHomeo_pj2A :
    scHomeo.hom ≫ pj2A = scSndHom Sph3T (TopCat.of (sphereInUnit 4)) := by
  ext p
  rfl

/-- **The pairing simplicial map `toSSet S³ ⊗ toSSet S³' ⟶ toSSet A` with its projections.** -/
theorem scZipMap :
    ∃ (φ : scPairObj SphX SphY ⟶ SphA),
      φ ≫ TopCat.toSSet.map pj1A = scPairFst SphX SphY
      ∧ φ ≫ TopCat.toSSet.map pj2A = scPairSnd SphX SphY := by
  refine ⟨scZip Sph3T (TopCat.of (sphereInUnit 4)) ≫ TopCat.toSSet.map scHomeo.hom, ?_, ?_⟩
  · rw [Category.assoc, ← Functor.map_comp, scHomeo_pj1A]
    exact scZip_fst _ _
  · rw [Category.assoc, ← Functor.map_comp, scHomeo_pj2A]
    exact scZip_snd _ _

/-! ## 2. Freeness of the homology of the spheres -/

/-- A homeomorphism transports path connectedness. -/
lemma scPathConnected_of_homeomorph {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) [PathConnectedSpace β] : PathConnectedSpace α := by
  rw [pathConnectedSpace_iff_univ]
  have h : IsPathConnected (Set.univ : Set β) := pathConnectedSpace_iff_univ.mp inferInstance
  have h2 := (e.symm.isPathConnected_image (s := Set.univ)).mpr h
  rwa [Set.image_univ_of_surjective e.symm.surjective] at h2

theorem scPathConnected_SphIn : PathConnectedSpace ↥(TopCat.of (sphereInUnit 4)) :=
  Work.Cohomology.sphereInUnit_pathConnected 4 (by norm_num)

theorem scPathConnected_Sph3T : PathConnectedSpace ↥Sph3T := by
  haveI := scPathConnected_SphIn
  exact scPathConnected_of_homeomorph (Work.Cohomology.sphereInUnitHomeomorph 4).symm

/-- `H₀` of a path-connected space is free (it is `ℤ`). -/
theorem scH0Free (X : TopCat) [PathConnectedSpace ↥X] :
    Module.Free ℤ ↥((singularChains ℤ X).homology 0) := by
  haveI : IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)) := inferInstance
  exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ)
    (Work.Cohomology.uctIsoToLinearEquiv
      (asIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)))).symm

/-- Freeness of the singular homology of the sphere `S³ ⊆ D⁴`. -/
theorem scFreeHomologySphIn (k : ℕ) :
    Module.Free ℤ ↥((singularChains ℤ (TopCat.of (sphereInUnit 4))).homology k) := by
  rcases eq_or_ne k 0 with rfl | h0
  · haveI := scPathConnected_SphIn
    exact scH0Free _
  · rcases eq_or_ne k 3 with rfl | hk3
    · obtain ⟨e'⟩ := sphereInUnitHomologyIso 4 3
      obtain ⟨e⟩ := sphereHomologyTop 3 (by norm_num)
      exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ)
        (uctIsoToLinearEquiv (e' ≪≫ e)).symm
    · obtain ⟨e'⟩ := sphereInUnitHomologyIso 4 k
      have hz : IsZero ((singularChains ℤ
          (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))).homology k) :=
        sphereHomologyZero 3 k (by norm_num) h0 hk3
      haveI : Subsingleton ↥((singularChains ℤ
          (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))).homology k) :=
        (ModuleCat.isZero_iff_subsingleton).mp hz
      exact Module.Free.of_equiv'
        (Module.Free.of_subsingleton ℤ
          ↥((singularChains ℤ
            (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))).homology k))
        (uctIsoToLinearEquiv e').symm

/-- Freeness of the singular homology of `Sph3T = S³`. -/
theorem scFreeHomologySph3T (k : ℕ) :
    Module.Free ℤ ↥((singularChains ℤ Sph3T).homology k) := by
  haveI := scFreeHomologySphIn k
  obtain ⟨e⟩ := sphereInUnitHomologyIso 4 k
  exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ
    ↥((singularChains ℤ (TopCat.of (sphereInUnit 4))).homology k))
    (uctIsoToLinearEquiv e)

/-! ## 3. Detecting cocycle and cycle on a space with free homology -/

/-- **A `3`-cocycle and a `3`-cycle with nonzero evaluation.** -/
theorem scDetectedPair (X : TopCat)
    (hfree : ∀ n, Module.Free ℤ ↥((singularChains ℤ X).homology n))
    (e : ↥((singularChains ℤ X).homology 3) ≃ₗ[ℤ] ℤ) :
    ∃ (α : Cochain ℤ (TopCat.toSSet.obj X) 3) (u : (singularChains ℤ X).X 3),
      cochainDiff ℤ (TopCat.toSSet.obj X) α = 0 ∧
      (((singularChains ℤ X).d 3 2).hom) u = 0 ∧ α u ≠ 0 := by
  have hbij := kronH_isIso X hfree 3
  obtain ⟨γ, hγeq⟩ := hbij.2 e.toLinearMap
  have hne : e.toLinearMap ≠ 0 := by
    intro h
    have h1 := congrArg (fun f => f (e.symm 1)) h
    simp only [LinearMap.zero_apply] at h1
    rw [show e.toLinearMap (e.symm 1) = e (e.symm 1) from rfl,
      LinearEquiv.apply_symm_apply] at h1
    exact one_ne_zero h1
  have hγ : γ ≠ 0 := by
    intro h0
    refine hne ?_
    rw [← hγeq, h0]
    exact map_zero _
  obtain ⟨u, α, hα, hu, _hclass, hαu⟩ := scExistsCycleEval X hfree γ hγ
  exact ⟨α, u, hα, hu, hαu⟩

/-! ## 4. `PInfty` agrees with the identity on cycles, at the chain level -/

/-- **The chain-level version of `Work.Cohomology.PInf_apply_cycle_eq`.** -/
lemma scPInf_apply_chain_eq (X : SSet) (c : Cn X 3) (hc : d32 X c = 0)
    (α : Cochain ℤ X 3) (hα : cochainDiff ℤ X α = 0) :
    α (PInf X 3 c) = α c := by
  set H := X.homotopyEquivNormalizedChainComplex ezR with hH
  have hcomm := congrArg (fun (f : (X.chainComplex ezR).X 3 ⟶ (X.chainComplex ezR).X 3) =>
    f.hom c) (H.homotopyHomInvId.comm 3)
  rw [HomologicalComplex.comp_f] at hcomm
  simp only [ModuleCat.hom_add, LinearMap.add_apply] at hcomm
  have hD : (ModuleCat.Hom.hom ((dNext 3) H.homotopyHomInvId.hom)) c = 0 := by
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel 3 2 from rfl), ModuleCat.hom_comp]
    simp only [LinearMap.comp_apply, hc, map_zero]
  rw [hD, zero_add] at hcomm
  rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel 4 3 from rfl)] at hcomm
  rw [ModuleCat.hom_comp] at hcomm
  simp only [LinearMap.comp_apply] at hcomm
  rw [show (ModuleCat.Hom.hom (((𝟙 (X.chainComplex ezR) :
      X.chainComplex ezR ⟶ X.chainComplex ezR)).f 3)) c = c
      from rfl] at hcomm
  have hhom : H.hom = X.toNormalizedChainComplex ezR := by
    rw [hH]; exact SSet.homotopyEquivNormalizedChainComplex_hom X ezR
  have hinv : H.inv = X.fromNormalizedChainComplex ezR := by
    rw [hH]; exact SSet.homotopyEquivNormalizedChainComplex_inv X ezR
  have hcomp : PInf X 3 c
      = (ModuleCat.Hom.hom (H.inv.f 3)) ((ModuleCat.Hom.hom (H.hom.f 3)) c) := by
    simp only [PInf, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      hhom, hinv]
  have hcomm' : (ModuleCat.Hom.hom (H.inv.f 3)) ((ModuleCat.Hom.hom (H.hom.f 3)) c)
      = ((X.chainComplex ezR).d 4 3).hom ((H.homotopyHomInvId.hom 3 4) c) + c := by
    rw [hcomm, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hzero : α (((X.chainComplex ezR).d 4 3).hom ((H.homotopyHomInvId.hom 3 4) c)) = 0 := by
    have h := congrArg (fun (g : (X.chainComplex ezR).X 4 →ₗ[ℤ] ℤ) =>
      g ((H.homotopyHomInvId.hom 3 4) c)) hα
    simpa only [cochainDiff, LinearMap.comp_apply, LinearMap.zero_apply] using h
  rw [hcomp, hcomm', map_add, hzero, zero_add]

/-! ## 5. A normalized detecting pair -/

/-- **A normalized `3`-cocycle and a `3`-cycle with nonzero evaluation.** -/
theorem scExistsNormalizedDetected (X : TopCat)
    (hfree : ∀ n, Module.Free ℤ ↥((singularChains ℤ X).homology n))
    (e : ↥((singularChains ℤ X).homology 3) ≃ₗ[ℤ] ℤ) :
    ∃ (θ : Cochain ℤ (TopCat.toSSet.obj X) 3) (d : (singularChains ℤ X).X 3),
      cochainDiff ℤ (TopCat.toSSet.obj X) θ = 0 ∧
      (((singularChains ℤ X).d 3 2).hom) d = 0 ∧ θ d ≠ 0 ∧
      (∀ x : (TopCat.toSSet.obj X) _⦋3⦌,
        x ∈ (TopCat.toSSet.obj X).degenerate 3 → genEval ℤ (TopCat.toSSet.obj X) θ x = 0) := by
  obtain ⟨α, u, hα, hu, hαu⟩ := scDetectedPair X hfree e
  refine ⟨α.comp (PInf (TopCat.toSSet.obj X) 3), u, ?_, hu, ?_, ?_⟩
  · exact cochainDiff_comp_PInf (TopCat.toSSet.obj X) α hα
  · rw [LinearMap.comp_apply]
    rw [scPInf_apply_chain_eq (TopCat.toSSet.obj X) u hu α hα]
    exact hαu
  · intro x hx
    simp only [genEval, LinearMap.comp_apply]
    rw [PInf_degenerate (TopCat.toSSet.obj X) x hx, map_zero]

/-! ## 6. Junk killing -/

/-- **A cochain vanishing on degenerate simplices kills the composites `Y.map g.op v` for
non-surjective monotone `g`.** -/
theorem scKills_of_normalized (Y : SSet) (θ : Cochain ℤ Y 3)
    (hn : ∀ x : Y _⦋3⦌, x ∈ Y.degenerate 3 → genEval ℤ Y θ x = 0) :
    ∀ (g : ⦋3⦌ ⟶ ⦋3⦌), ¬ Function.Surjective ⇑(ConcreteCategory.hom g) →
      ∀ v : Y _⦋3⦌, genEval ℤ Y θ ((ConcreteCategory.hom (Y.map g.op)) v) = 0 := by
  intro g hg v
  apply hn
  refine Work.Crux33.mem_degenerate_of_not_injective 2 g ?_ v
  intro hinj
  exact hg ((Finite.injective_iff_surjective).mp hinj)

/-! ## 7. Pullback bookkeeping -/

/-- Pullback along a simplicial map is functorial. -/
lemma scSsetPullback_comp (X Y Z : SSet) (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (γ : Cochain ℤ Z n) :
    Kunneth.ssetPullback X Z (f ≫ g) n γ
      = Kunneth.ssetPullback X Y f n (Kunneth.ssetPullback Y Z g n γ) := by
  apply cup_ext ℤ X
  intro σ
  rw [Kunneth.ssetPullback_genEval, Kunneth.ssetPullback_genEval,
    Kunneth.ssetPullback_genEval]
  rfl

/-- Naturality of the Alexander–Whitney cup product, in the `ssetPullback` spelling. -/
lemma scCupNatural (X Y : SSet) (f : X ⟶ Y) (α β : Cochain ℤ Y 3) :
    cup ℤ X (Kunneth.ssetPullback X Y f 3 α) (Kunneth.ssetPullback X Y f 3 β)
      = Kunneth.ssetPullback X Y f 6 (cup ℤ Y α β) := by
  apply cup_ext ℤ X
  intro σ
  rw [cup_apply, Kunneth.ssetPullback_genEval, Kunneth.ssetPullback_genEval,
    Kunneth.ssetPullback_genEval, app_frontFace, app_backFace, cup_apply]

/-- The Kronecker pairing of a pulled-back cochain with a pushed-forward chain is the pairing of
the original cochain with the original chain. -/
lemma scKronecker_push (X Y : SSet) (f : X ⟶ Y) (n : ℕ) (γ : Cochain ℤ Y n)
    (w : (X.chainComplex ezR).X n) :
    kronecker ℤ Y γ (((SSet.chainComplexMap f ezR).f n).hom w)
      = kronecker ℤ X (Kunneth.ssetPullback X Y f n γ) w := rfl

/-- The coboundary commutes with the transpose of a map of simplicial sets. -/
lemma scCdiffDualMap (X Y : SSet) (f : X ⟶ Y) (n : ℕ) (φ : Cochain ℤ Y n) :
    (((SSet.chainComplexMap f ezR).f (n + 1)).hom.dualMap (cochainDiff ℤ Y φ))
      = cochainDiff ℤ X ((((SSet.chainComplexMap f ezR).f n).hom.dualMap φ)) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.dualMap_apply, cochainDiff, LinearMap.comp_apply]
  congr 1
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom ((SSet.chainComplexMap f ezR).comm (n + 1) n)) x

/-- The pullback of a cocycle along a continuous map is a cocycle. -/
theorem scPullback_cocycle (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj Y) n)
    (hφ : cochainDiff ℤ (TopCat.toSSet.obj Y) φ = 0) :
    cochainDiff ℤ (TopCat.toSSet.obj X)
      ((cochainPullbackHom ℤ X Y f n).hom φ) = 0 := by
  show cochainDiff ℤ (TopCat.toSSet.obj X)
    (((SSet.chainComplexMap (TopCat.toSSet.map f) ezR).f n).hom.dualMap φ) = 0
  rw [← scCdiffDualMap (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) (TopCat.toSSet.map f) n φ,
    hφ, map_zero]

/-! ## 8. Graded commutativity of the cup product, on a cycle -/

/-- **The cup product is graded-commutative on cycles, in degree `(3,3)`.** -/
theorem scCupSwapEval (X : SSet) (α₁ α₂ : Cochain ℤ X 3)
    (h₁ : cochainDiff ℤ X α₁ = 0) (h₂ : cochainDiff ℤ X α₂ = 0)
    (z : (X.chainComplex ezR).X 6) (hz : ((X.chainComplex ezR).d 6 5) z = 0) :
    kronecker ℤ X (cup ℤ X α₂ α₁) z = - kronecker ℤ X (cup ℤ X α₁ α₂) z := by
  obtain hh : 3 + 3 - 1 + 1 = 3 + 3 := Nat.sub_add_cancel (by norm_num)
  have hid := cup1IdentityA ℤ X 3 3 (by norm_num) (by norm_num) hh α₁ α₂ h₁ h₂
  have hcast : (((Nat.add_comm 3 3 : 3 + 3 = 3 + 3)) ▸ (cup ℤ X α₂ α₁ : Cochain ℤ X (3 + 3)))
      = cup ℤ X α₂ α₁ := by
    rw [Subsingleton.elim (Nat.add_comm 3 3 : 3 + 3 = 3 + 3) rfl]
  have hid' : cochainDiff ℤ X (cup1 ℤ X 3 3 α₁ α₂)
      = cup ℤ X α₁ α₂ - (-1 : ℤ) • cup ℤ X α₂ α₁ := by
    have h := hid
    rw [Subsingleton.elim hh rfl, hcast, show (-1 : ℤ) ^ (3 * 3) = -1 from by norm_num] at h
    simpa using h
  have hzero : (cochainDiff ℤ X (cup1 ℤ X 3 3 α₁ α₂)) z = 0 := by
    show (cup1 ℤ X 3 3 α₁ α₂) ((X.chainComplex ezR).d 6 5 z) = 0
    rw [hz, map_zero]
  show (cup ℤ X α₂ α₁) z = - (cup ℤ X α₁ α₂) z
  have h := congrArg (fun (γ : Cochain ℤ X 6) => γ z) hid'
  rw [hzero, LinearMap.sub_apply, LinearMap.smul_apply] at h
  have hb : (-1 : ℤ) • ((cup ℤ X α₂ α₁) z) = - ((cup ℤ X α₂ α₁) z) := by
    rw [neg_smul, one_smul]
  rw [hb] at h
  linarith

/-! ## 9. The witnesses -/

/-- The isomorphism `H₃(S³) ≅ ℤ` for `Sph3T`. -/
theorem scHomology3IsoSph3T :
    Nonempty (↥((singularChains ℤ Sph3T).homology 3) ≃ₗ[ℤ] ℤ) := by
  obtain ⟨e⟩ := sphereHomologyTop 3 (by norm_num)
  exact ⟨uctIsoToLinearEquiv e⟩

/-- The isomorphism `H₃(S³) ≅ ℤ` for the sphere `S³ ⊆ D⁴`. -/
theorem scHomology3IsoSphIn :
    Nonempty (↥((singularChains ℤ (TopCat.of (sphereInUnit 4))).homology 3) ≃ₗ[ℤ] ℤ) := by
  obtain ⟨e⟩ := sphereHomologyTop 3 (by norm_num)
  obtain ⟨e'⟩ := sphereInUnitHomologyIso 4 3
  exact ⟨uctIsoToLinearEquiv (e' ≪≫ e)⟩

/-- **The Künneth witness in the order in which the shuffle evaluation produces it.** -/
theorem scKunnethWitness :
    ∃ (θ' : Cochain ℤ SphY 3) (β : Cochain ℤ SphX 3)
      (a : (SphA.chainComplex ezR).X 6),
      cochainDiff ℤ SphY θ' = 0
      ∧ cochainDiff ℤ SphX β = 0
      ∧ (SphA.chainComplex ezR).d 6 5 a = 0
      ∧ kronecker ℤ SphA
          (cup ℤ SphA
            ((cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom θ')
            ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β))
          a ≠ 0 := by
  obtain ⟨e1⟩ := scHomology3IsoSph3T
  obtain ⟨e2⟩ := scHomology3IsoSphIn
  obtain ⟨β, c, hβ, hc, hβc⟩ := scDetectedPair Sph3T scFreeHomologySph3T e1
  obtain ⟨θ, d, hθ, hd, hθd, hnorm⟩ := scExistsNormalizedDetected
    (TopCat.of (sphereInUnit 4)) scFreeHomologySphIn e2
  have hkill := scKills_of_normalized SphY θ hnorm
  obtain ⟨φ, hφ1, hφ2⟩ := scZipMap
  set w := Kunneth.ezChain SphX SphY c d with hw
  set a := ((SSet.chainComplexMap φ ezR).f 6).hom w with ha
  have hcyc : ((scPairObj SphX SphY).chainComplex ezR).d 6 5
      (Kunneth.ezChain SphX SphY c d) = 0 :=
    scEzChain_isCycle SphX SphY c d hc hd
  have hacyc : (SphA.chainComplex ezR).d 6 5 a = 0 := by
    rw [ha]
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.Hom.comm (SSet.chainComplexMap φ ezR) 6 5)) w
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, hw, hcyc, map_zero]
  have heval : kronecker ℤ SphA
      (cup ℤ SphA
        ((cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom θ)
        ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β)) a
      = - (β c) * (θ d) := by
    rw [ha, hw]
    have h1 : kronecker ℤ SphA
        (cup ℤ SphA
          ((cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom θ)
          ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β))
        (((SSet.chainComplexMap φ ezR).f 6).hom (Kunneth.ezChain SphX SphY c d))
        = kronecker ℤ (scPairObj SphX SphY)
            (Kunneth.ssetPullback (scPairObj SphX SphY) SphA φ 6
              (cup ℤ SphA
                ((cochainPullbackHom ℤ (TopCat.of PairAT)
                  (TopCat.of (sphereInUnit 4)) pj2A 3).hom θ)
                ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β)))
            (Kunneth.ezChain SphX SphY c d) :=
      scKronecker_push (scPairObj SphX SphY) SphA φ 6 _ _
    have h2 : Kunneth.ssetPullback (scPairObj SphX SphY) SphA φ 6
        (cup ℤ SphA
          ((cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom θ)
          ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β))
        = cup ℤ (scPairObj SphX SphY)
            (Kunneth.ssetPullback (scPairObj SphX SphY) SphA φ 3
              ((cochainPullbackHom ℤ (TopCat.of PairAT)
                (TopCat.of (sphereInUnit 4)) pj2A 3).hom θ))
            (Kunneth.ssetPullback (scPairObj SphX SphY) SphA φ 3
              ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β)) :=
      (scCupNatural (scPairObj SphX SphY) SphA φ _ _).symm
    have h3 : Kunneth.ssetPullback (scPairObj SphX SphY) SphA φ 3
        ((cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom θ)
        = scPullSnd SphX SphY 3 θ := by
      show Kunneth.ssetPullback (scPairObj SphX SphY) SphA φ 3
          (Kunneth.ssetPullback SphA SphY (TopCat.toSSet.map pj2A) 3 θ) = _
      rw [← scSsetPullback_comp (scPairObj SphX SphY) SphA SphY φ (TopCat.toSSet.map pj2A) 3 θ,
        hφ2]
    have h4 : Kunneth.ssetPullback (scPairObj SphX SphY) SphA φ 3
        ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β)
        = scPullFst SphX SphY 3 β := by
      show Kunneth.ssetPullback (scPairObj SphX SphY) SphA φ 3
          (Kunneth.ssetPullback SphA SphX (TopCat.toSSet.map pj1A) 3 β) = _
      rw [← scSsetPullback_comp (scPairObj SphX SphY) SphA SphX φ (TopCat.toSSet.map pj1A) 3 β,
        hφ1]
    rw [h1, h2, h3, h4]
    exact scEzChainEval SphX SphY β θ c d hkill
  exact ⟨θ, β, a, hθ, hβ, hacyc, by
    rw [heval]
    exact mul_ne_zero (neg_ne_zero.mpr hβc) hθd⟩

/-- **The target witnesses**, in the order of the statement of `sph3DiscCupEval`. -/
theorem scTargetWitness :
    ∃ (β : Cochain ℤ (TopCat.toSSet.obj Sph3T) 3)
      (β' : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (sphereInUnit 4))) 3)
      (Δ : (singularChains ℤ (TopCat.of PairAT)).X 6),
      cochainDiff ℤ (TopCat.toSSet.obj Sph3T) β = 0
      ∧ cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (sphereInUnit 4))) β' = 0
      ∧ (singularChains ℤ (TopCat.of PairAT)).d 6 5 Δ = 0
      ∧ kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
          (cup ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
            ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β)
            ((cochainPullbackHom ℤ (TopCat.of PairAT)
              (TopCat.of (sphereInUnit 4)) pj2A 3).hom β'))
          Δ ≠ 0 := by
  obtain ⟨θ, β, a, hθ, hβ, ha, hev⟩ := scKunnethWitness
  refine ⟨β, θ, a, hβ, hθ, ha, ?_⟩
  have h₁ : cochainDiff ℤ SphA
      ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β) = 0 :=
    scPullback_cocycle (TopCat.of PairAT) Sph3T pj1A 3 β hβ
  have h₂ : cochainDiff ℤ SphA
      ((cochainPullbackHom ℤ (TopCat.of PairAT)
        (TopCat.of (sphereInUnit 4)) pj2A 3).hom θ) = 0 :=
    scPullback_cocycle (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3 θ hθ
  intro hzero
  refine hev ?_
  rw [scCupSwapEval SphA
    ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β)
    ((cochainPullbackHom ℤ (TopCat.of PairAT)
      (TopCat.of (sphereInUnit 4)) pj2A 3).hom θ)
    h₁ h₂ a ha, hzero, neg_zero]

end

end Work.Cohomology.Crux33
