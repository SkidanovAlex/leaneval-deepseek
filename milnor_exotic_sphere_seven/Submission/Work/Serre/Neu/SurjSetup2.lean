-- PORTED COPY (neutral island) of `Submission/Work/Serre/Surj/Setup2.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.SurjSetup
import Submission.Work.Serre.Neu.SurjDefs
import Submission.Work.Serre.Neu.RatHyp
import Submission.Work.Serre.crossProduct_coker_rat
import Submission.Work.StemsB.WangCohRat
import Submission.Work.Serre.Neu.SurjBaseChange

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## Naturality of the base change with respect to an inclusion -/

/-- Naturality of the base change of the absolute chains with respect to an inclusion of
subspaces. -/
theorem bcAbs_incl (X : TopCat) (A : Set X) :
    Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A) ≫ (bcAbs ↥X).hom
      = (bcAbs ↥A).hom ≫ Work.StemsB.relChainsRIncl ℚ X A :=
  (Work.StemsB.RatBC.Phi_naturality
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))).symm

/-! ## The rational relative cycle attached to an integral lift -/

/-- The base change of an integral chain of `P`, viewed as a rational chain of `P`. -/
noncomputable def vt0Of (P : Type) [TopologicalSpace P] (r : ℕ)
    (vtz : ↥((Work.Cohomology.singularChains ℤ (TopCat.of P)).X (r + 1))) :
    ↥((Work.Cohomology.singularChains ℚ (TopCat.of P)).X (r + 1)) :=
  (ModuleCat.Hom.hom ((bcAbs P).hom.f (r + 1))) (TensorProduct.tmul ℤ (1 : ℚ) vtz)

/-- the differential of `vt0Of` is the base change of the differential of `vtz`. -/
theorem d_vt0Of (P : Type) [TopologicalSpace P] (r : ℕ)
    (vtz : ↥((Work.Cohomology.singularChains ℤ (TopCat.of P)).X (r + 1))) :
    (ModuleCat.Hom.hom ((Work.Cohomology.singularChains ℚ (TopCat.of P)).d (r + 1) r))
        (vt0Of P r vtz)
      = (ModuleCat.Hom.hom ((bcAbs P).hom.f r))
          (TensorProduct.tmul ℤ (1 : ℚ)
            ((ModuleCat.Hom.hom
              ((Work.Cohomology.singularChains ℤ (TopCat.of P)).d (r + 1) r)) vtz)) := by
  have h := congrArg (fun g => (ModuleCat.Hom.hom g) (TensorProduct.tmul ℤ (1 : ℚ) vtz))
    (HomologicalComplex.Hom.comm (bcAbs P).hom (r + 1) r)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  unfold vt0Of
  rw [h]
  exact congrArg _ (IntRatCM_d_tmul _ (r + 1) r vtz)

/-- **The rational relative cycle attached to an integral lift of `z`.** -/
noncomputable def v0Of (P : Type) [TopologicalSpace P] (Q : Set P) (r : ℕ)
    (z : ↥((Work.Cohomology.relChains (TopCat.of P) Q).cycles (r + 1)))
    (vtz : ↥((Work.Cohomology.singularChains ℤ (TopCat.of P)).X (r + 1)))
    (hvtz : (ModuleCat.Hom.hom ((Work.Cohomology.relChainsProj (TopCat.of P) Q).f (r + 1))) vtz
      = (ModuleCat.Hom.hom ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles (r + 1))) z) :
    ↥((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).cycles (r + 1)) :=
  cycleOfQ (Work.StemsB.relChainsR ℚ (TopCat.of P) Q) (r + 1)
    (Work.StemsB.rdRProj ℚ (TopCat.of P) Q (r + 1) (vt0Of P r vtz)) (by
      show (ModuleCat.Hom.hom ((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).d (r + 1) r))
          ((ModuleCat.Hom.hom (Work.StemsB.rdRProj ℚ (TopCat.of P) Q (r + 1)))
            (vt0Of P r vtz)) = 0
      rw [← LinearMap.comp_apply, Work.StemsB.rdRProj_comm_lm, LinearMap.comp_apply]
      rw [d_vt0Of]
      have hker : (ModuleCat.Hom.hom ((Work.Cohomology.relChainsProj (TopCat.of P) Q).f r))
          ((ModuleCat.Hom.hom
            ((Work.Cohomology.singularChains ℤ (TopCat.of P)).d (r + 1) r)) vtz) = 0 := by
        have h := congrArg (fun g => (ModuleCat.Hom.hom g) vtz)
          (HomologicalComplex.Hom.comm (Work.Cohomology.relChainsProj (TopCat.of P) Q) (r + 1) r)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
        rw [← h, hvtz]
        have h2 := congrArg (fun (g : (Work.Cohomology.relChains (TopCat.of P) Q).cycles (r + 1) ⟶
            (Work.Cohomology.relChains (TopCat.of P) Q).X r) => (ModuleCat.Hom.hom g) z)
          (HomologicalComplex.iCycles_d (Work.Cohomology.relChains (TopCat.of P) Q) (r + 1) r)
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
          LinearMap.zero_apply] using h2
      have hmem : ((ModuleCat.Hom.hom
            ((Work.Cohomology.singularChains ℤ (TopCat.of P)).d (r + 1) r)) vtz)
          ∈ LinearMap.range ((Work.StemsB.relChainsRIncl ℤ (TopCat.of P) Q).f r).hom := by
        rw [← Work.StemsB.rdRProj_ker ℤ (TopCat.of P) Q r]
        exact hker
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
      rw [← hy]
      have key : (ModuleCat.Hom.hom ((bcAbs P).hom.f r))
            (TensorProduct.tmul ℤ (1 : ℚ)
              ((ModuleCat.Hom.hom
                ((Work.StemsB.relChainsRIncl ℤ (TopCat.of P) Q).f r)) y))
          = (ModuleCat.Hom.hom ((Work.StemsB.relChainsRIncl ℚ (TopCat.of P) Q).f r))
              ((ModuleCat.Hom.hom ((bcAbs ↥Q).hom.f r)) (TensorProduct.tmul ℤ (1 : ℚ) y)) := by
        rw [← IntRatCM_map_tmul]
        have h := congrArg (fun g => (ModuleCat.Hom.hom (g.f r)) (TensorProduct.tmul ℤ (1 : ℚ) y))
          (bcAbs_incl (TopCat.of P) Q)
        simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
        rw [IntRatCM_map_tmul] at h
        exact h
      rw [key]
      exact Work.StemsB.rdRProj_incl_apply ℚ (TopCat.of P) Q r _)

/-! ## The value of the shuffle on a rational cycle class -/

/-- **The value of the relative projection of the shuffle.** -/
theorem shuffleProjection (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (Q : Set P) (r m : ℕ)
    (z : ↥((Work.Cohomology.relChains (TopCat.of P) Q).cycles (r + 1)))
    (vtz : ↥((Work.Cohomology.singularChains ℤ (TopCat.of P)).X (r + 1)))
    (hvtz : (ModuleCat.Hom.hom ((Work.Cohomology.relChainsProj (TopCat.of P) Q).f (r + 1))) vtz
      = (ModuleCat.Hom.hom ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles (r + 1))) z)
    (w : ↥((Work.Cohomology.singularChains ℤ (TopCat.of W)).cycles m))
    (q : ℚ)
    (u : ↥((Work.Cohomology.singularChains ℚ (TopCat.of W)).cycles m))
    (hu : (ModuleCat.Hom.hom ((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m)) u
      = q • (ModuleCat.Hom.hom ((bcAbs W).hom.f m))
            (TensorProduct.tmul ℤ (1 : ℚ)
              ((ModuleCat.Hom.hom
                ((Work.Cohomology.singularChains ℤ (TopCat.of W)).iCycles m)) w))) :
    (Work.StemsB.rdRProj ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1))
        (Work.Serre.shufRat W P m (r + 1)
          ((ModuleCat.Hom.hom ((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m)) u)
          (vt0Of P r vtz))
      = q • (ModuleCat.Hom.hom
          ((bcRel (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).hom.f (m + r + 1)))
          (TensorProduct.tmul ℤ (1 : ℚ)
            ((ModuleCat.Hom.hom ((Work.Cohomology.relChainsProj (TopCat.of (W × P))
              {x : W × P | x.2 ∈ Q}).f (m + r + 1)))
              (Work.Serre.ezShufChain W P m (r + 1)
                ((ModuleCat.Hom.hom
                  ((Work.Cohomology.singularChains ℤ (TopCat.of W)).iCycles m)) w) vtz))) := by
  have h1 : Work.Serre.shufRat W P m (r + 1)
        ((ModuleCat.Hom.hom ((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m)) u)
        (vt0Of P r vtz)
      = q • (ModuleCat.Hom.hom ((bcAbs (W × P)).hom.f (m + r + 1)))
          (TensorProduct.tmul ℤ (1 : ℚ)
            (Work.Serre.ezShufChain W P m (r + 1)
              ((ModuleCat.Hom.hom
                ((Work.Cohomology.singularChains ℤ (TopCat.of W)).iCycles m)) w) vtz)) := by
    rw [hu]
    simp only [map_smul, LinearMap.smul_apply]
    congr 1
    unfold vt0Of
    exact (Work.Serre.Surj.baseChangeEzShufChain W P m (r + 1)
      ((ModuleCat.Hom.hom ((Work.Cohomology.singularChains ℤ (TopCat.of W)).iCycles m)) w) vtz).symm
  rw [h1, map_smul]
  rw [show (Work.StemsB.rdRProj ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1))
        ((ModuleCat.Hom.hom ((bcAbs (W × P)).hom.f (m + r + 1)))
          (TensorProduct.tmul ℤ (1 : ℚ)
            (Work.Serre.ezShufChain W P m (r + 1)
              ((ModuleCat.Hom.hom
                ((Work.Cohomology.singularChains ℤ (TopCat.of W)).iCycles m)) w) vtz)))
      = (ModuleCat.Hom.hom
          ((bcRel (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}).hom.f (m + r + 1)))
          (TensorProduct.tmul ℤ (1 : ℚ)
            ((ModuleCat.Hom.hom ((Work.Cohomology.relChainsProj (TopCat.of (W × P))
              {x : W × P | x.2 ∈ Q}).f (m + r + 1)))
              (Work.Serre.ezShufChain W P m (r + 1)
                ((ModuleCat.Hom.hom
                  ((Work.Cohomology.singularChains ℤ (TopCat.of W)).iCycles m)) w) vtz)))
      from (bcRel_value (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1) _).symm]

end

end Work.Serre.Surj

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Cohomology

/-! ## Rational chain complexes: naturality of the cycles -/

/-- The underlying chain of the image of a cycle under a chain map of rational complexes. -/
theorem iCycles_cyclesMap_q (K L : ChainComplex (ModuleCat ℚ) ℕ) (f : K ⟶ L) (n : ℕ)
    (x : ↥(K.cycles n)) :
    (ModuleCat.Hom.hom (L.iCycles n)) ((HomologicalComplex.cyclesMap f n) x)
      = (ModuleCat.Hom.hom (f.f n)) ((ModuleCat.Hom.hom (K.iCycles n)) x) := by
  have h := congrArg (fun (g : K.cycles n ⟶ L.X n) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.cyclesMap_i f n)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The value of `homologyMap` on the class of a cycle, for rational complexes. -/
theorem homologyMap_homologyπ_q (K L : ChainComplex (ModuleCat ℚ) ℕ) (f : K ⟶ L) (n : ℕ)
    (x : ↥(K.cycles n)) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap f n))
        ((ModuleCat.Hom.hom (K.homologyπ n)) x)
      = (ModuleCat.Hom.hom (L.homologyπ n)) ((HomologicalComplex.cyclesMap f n) x) := by
  have h := congrArg (fun (g : K.cycles n ⟶ L.homology n) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.homologyπ_naturality (φ := f) (i := n))
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h

end

end Work.Serre.Surj

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The cokernel of an isomorphism, tensored with `ℚ`, is a subsingleton. -/
theorem subsingleton_coker_tensor_of_isIso {A B : ModuleCat ℤ} (f : A ⟶ B) [IsIso f] :
    Subsingleton (TensorProduct ℤ ↥(CategoryTheory.Limits.cokernel f) ℚ) := by
  haveI : Epi f := inferInstance
  have hπ0 : CategoryTheory.Limits.cokernel.π f = 0 := by
    apply (cancel_epi f).mp
    rw [CategoryTheory.Limits.cokernel.condition, comp_zero]
  have hzero : (CategoryTheory.Limits.cokernel.π f).hom = 0 := by
    rw [hπ0]
    rfl
  have hsub : Subsingleton (↥(CategoryTheory.Limits.cokernel f)) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := (ModuleCat.epi_iff_surjective
      (CategoryTheory.Limits.cokernel.π f)).mp inferInstance x
    obtain ⟨y', rfl⟩ := (ModuleCat.epi_iff_surjective
      (CategoryTheory.Limits.cokernel.π f)).mp inferInstance y
    rw [show (CategoryTheory.Limits.cokernel.π f).hom x' = 0 from by rw [hzero]; rfl,
      show (CategoryTheory.Limits.cokernel.π f).hom y' = 0 from by rw [hzero]; rfl]
  haveI := hsub
  refine ⟨fun x y => ?_⟩
  have hz : ∀ z : TensorProduct ℤ ↥(CategoryTheory.Limits.cokernel f) ℚ, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a q => rw [Subsingleton.elim a (0 : ↥(CategoryTheory.Limits.cokernel f)),
        TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [hz x, hz y]

end

end Work.Serre.Surj

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- Two cycles of a rational chain complex with the same underlying chain are equal. -/
theorem cycle_eq_of_iCycles_eq (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    {x y : ↥(K.cycles n)}
    (h : (ModuleCat.Hom.hom (K.iCycles n)) x = (ModuleCat.Hom.hom (K.iCycles n)) y) : x = y :=
  ((ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance) h

end

end Work.Serre.Surj
