import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.relComplexIsoDual
import Submission.Work.Cohomology.kronecker_descent
import Submission.Work.Cohomology.cupH
import Submission.Work.Cohomology.relCapH_kronH_cup

/-!
# The relative Kronecker pairing: the chain-variable half

For a pair `(X,A)` of topological spaces the relative singular cochains `C^*(X,A) = ker(restr)` are
the duals of the relative singular chains `C_*(X,A) = cokernel(inclChains)`
(`Work.Cohomology.relCochainDual`, `Work.Cohomology.relDualEquiv`); this module descends that
degreewise pairing to (co)homology and proves the computation rule

  `⟨[α], [cc]⟩ = α.1(zhat)`

for a relative `n`-cocycle `α`, a relative `n`-cycle `cc` and any absolute `n`-chain `zhat` lifting
`cc`.  This is the relative analogue of `Work.Cohomology.kronecker_descent`, whose proof is followed
step by step; it is the pairing that the (mixed) cap/cup adjunction of the tubular chapter needs
(`Work.Tubular.kronH_mixedCup_relKronH`), because the cap product of a relative class with a
relative cycle lands in the *absolute* homology of `X`, so it may only be paired with a class of the
*absolute* cohomology of `X` — whereas the mixed product `x ⌣ β` is a *relative* class, whose
canonical partner is the relative pairing defined here.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Tubular

noncomputable section

open Work.Cohomology

/-! ## The chain-level pairing -/

/-- The functional on the relative chains associated with a relative cochain: the inverse of the
degreewise isomorphism `Work.Cohomology.relDualEquiv`. -/
noncomputable def relKronLM (X : TopCat) (A : Set X) (n : ℕ) :
    relKern ℤ X A n →ₗ[ℤ] ((relChains X A).X n →ₗ[ℤ] ℤ) :=
  (relDualEquiv X A n).symm

/-- The value of `relKronLM` on the image of a lift. -/
theorem relKronLM_relDualProj (X : TopCat) (A : Set X) (n : ℕ) (φ : relKern ℤ X A n)
    (x : (singularChains ℤ X).X n) :
    relKronLM X A n φ ((relDualProj X A n) x) = relDualLM X n φ.1 x := by
  have h := LinearMap.congr_fun (relDualEquiv_symm_comp X A n φ) x
  rw [LinearMap.comp_apply] at h
  exact h

/-- The chain-level relative pairing of a relative cochain with the cycles of the relative chains. -/
def relKronCycEval (X : TopCat) (A : Set X) (n : ℕ) (φ : relKern ℤ X A n) :
    (relChains X A).cycles n →ₗ[ℤ] ℤ :=
  (relKronLM X A n φ).comp ((relChains X A).iCycles n).hom

/-- The `iCycles` of the boundary is the differential. -/
lemma iCycles_toCycles_relChains (X : TopCat) (A : Set X) (i j : ℕ)
    (y : (relChains X A).X i) :
    ((relChains X A).iCycles j).hom (((relChains X A).toCycles i j) y)
      = ((relChains X A).d i j).hom y := by
  have h := congrArg (fun (g : (relChains X A).X i ⟶ (relChains X A).X j) => g.hom y)
    (HomologicalComplex.toCycles_i (relChains X A) i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- **A relative cocycle pairs to zero with a relative boundary**: the descent in the chain
variable. -/
lemma toCycles_relKronCycEval (X : TopCat) (A : Set X) (n : ℕ) (φ : relKern ℤ X A n)
    (hφ : relDiffLM ℤ X A n φ = 0) :
    (relChains X A).toCycles (n + 1) n ≫ ModuleCat.ofHom (relKronCycEval X A n φ) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  show relKronCycEval X A n φ (((relChains X A).toCycles (n + 1) n) y) = 0
  rw [relKronCycEval, LinearMap.comp_apply, iCycles_toCycles_relChains]
  obtain ⟨ŷ, hŷ⟩ := relDualProj_surjective X A (n + 1) y
  rw [← hŷ]
  have hcomm : ((relChains X A).d (n + 1) n) ((relDualProj X A (n + 1)) ŷ)
      = (relDualProj X A n) (((singularChains ℤ X).d (n + 1) n) ŷ) :=
    LinearMap.congr_fun (relDualProj_comm_lm X A n) ŷ
  rw [hcomm, relKronLM_relDualProj, ← relDualDiff_apply X A n φ ŷ]
  have h2 : (relDiff ℤ X A n φ).1 = 0 := by
    rw [show (relDiff ℤ X A n φ : relKern ℤ X A (n + 1)) = relDiffLM ℤ X A n φ from rfl, hφ]
    simp
  rw [h2]
  simp [relDualLM]

/-- **Descent in the chain variable.**  The functional on the relative cycles given by a relative
*cocycle* factors through the relative homology. -/
noncomputable def relKronCocycDesc (X : TopCat) (A : Set X) (n : ℕ) (φ : relKern ℤ X A n)
    (hφ : relDiffLM ℤ X A n φ = 0) : (relChains X A).homology n ⟶ ModuleCat.of ℤ ℤ :=
  ((relChains X A).homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n)).desc
    (CokernelCofork.ofπ (ModuleCat.ofHom (relKronCycEval X A n φ))
      (toCycles_relKronCycEval X A n φ hφ))

/-- Computation rule for `relKronCocycDesc`. -/
lemma homologyπ_relKronCocycDesc (X : TopCat) (A : Set X) (n : ℕ) (φ : relKern ℤ X A n)
    (hφ : relDiffLM ℤ X A n φ = 0) :
    (relChains X A).homologyπ n ≫ relKronCocycDesc X A n φ hφ
      = ModuleCat.ofHom (relKronCycEval X A n φ) :=
  Cofork.IsColimit.π_desc
    (s := CokernelCofork.ofπ ((relChains X A).homologyπ n)
      (HomologicalComplex.toCycles_comp_homologyπ (relChains X A) (n + 1) n))
    (t := CokernelCofork.ofπ (ModuleCat.ofHom (relKronCycEval X A n φ))
      (toCycles_relKronCycEval X A n φ hφ))
    (((relChains X A).homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n)))

/-- Computation rule for `relKronCocycDesc` on the class of a relative cycle. -/
lemma relKronCocycDesc_apply (X : TopCat) (A : Set X) (n : ℕ) (φ : relKern ℤ X A n)
    (hφ : relDiffLM ℤ X A n φ = 0) (c : (relChains X A).cycles n) :
    (relKronCocycDesc X A n φ hφ).hom (((relChains X A).homologyπ n) c)
      = relKronLM X A n φ (((relChains X A).iCycles n) c) := by
  have h := congrArg (fun (g : (relChains X A).cycles n ⟶ ModuleCat.of ℤ ℤ) => g.hom c)
    (homologyπ_relKronCocycDesc X A n φ hφ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    relKronCycEval, LinearMap.comp_apply] at h
  exact h

/-! ## The pairing of a relative cocycle with the relative homology -/

/-- The relative cochain underlying a cycle of the relative cochain complex. -/
def relOfCycle (X : TopCat) (A : Set X) (n : ℕ) (z : (relComplex ℤ X A).cycles n) :
    relKern ℤ X A n :=
  ((relComplex ℤ X A).iCycles n).hom z

/-- A cycle of the relative cochain complex is a relative cocycle. -/
lemma relDiffLM_relOfCycle (X : TopCat) (A : Set X) (n : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    relDiffLM ℤ X A n (relOfCycle X A n z) = 0 :=
  relDiffLM_iCycles X A n z

/-- The relative cochain underlying a relative cycle, as a linear map in the cycle. -/
noncomputable def relOfCycleLin (X : TopCat) (A : Set X) (n : ℕ) :
    (relComplex ℤ X A).cycles n →ₗ[ℤ] relKern ℤ X A n :=
  ((relComplex ℤ X A).iCycles n).hom

/-- The functional on the relative cycles associated with a relative cochain, as a linear map. -/
noncomputable def relKronCycEvalLin (X : TopCat) (A : Set X) (n : ℕ) :
    relKern ℤ X A n →ₗ[ℤ] ((relChains X A).cycles n →ₗ[ℤ] ℤ) :=
  (LinearMap.lcomp (S := ℤ) (N := ℤ) ((relChains X A).iCycles n).hom).comp (relKronLM X A n)

/-- The pairing on the cycles, linear in *both* variables (no `map_smul'` is proved by hand: it is a
composite of existing `LinearMap`s). -/
noncomputable def relKronFunLin (X : TopCat) (A : Set X) (n : ℕ) :
    (relComplex ℤ X A).cycles n →ₗ[ℤ] ((relChains X A).cycles n →ₗ[ℤ] ℤ) :=
  (relKronCycEvalLin X A n).comp (relOfCycleLin X A n)

/-- The computation rule for `relKronFunLin`. -/
lemma relKronFunLin_apply (X : TopCat) (A : Set X) (n : ℕ)
    (z : (relComplex ℤ X A).cycles n) (c : (relChains X A).cycles n) :
    relKronFunLin X A n z c
      = relKronLM X A n (relOfCycle X A n z) (((relChains X A).iCycles n) c) := by
  show ((relKronLM X A n (relOfCycle X A n z)).comp ((relChains X A).iCycles n).hom) c
      = relKronLM X A n (relOfCycle X A n z) (((relChains X A).iCycles n) c)
  rfl

/-- The factorisation of the functional of a relative cycle through the homology of the relative
chains: the descent in the *chain* variable, applied to the relative cocycle of the relative cycle. -/
noncomputable def relKronDesc (X : TopCat) (A : Set X) (n : ℕ)
    (z : (relComplex ℤ X A).cycles n) : (relChains X A).homology n ⟶ ModuleCat.of ℤ ℤ :=
  relKronCocycDesc X A n (relOfCycle X A n z) (relDiffLM_relOfCycle X A n z)

/-- The defining property of `relKronDesc`: composed with the homology projection it is
`relKronFunLin`. -/
lemma relKronDesc_comp_homologyπ (X : TopCat) (A : Set X) (n : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    (relKronDesc X A n z).hom.comp (((relChains X A).homologyπ n).hom)
      = relKronFunLin X A n z := by
  have h := congrArg ModuleCat.Hom.hom
    (homologyπ_relKronCocycDesc X A n (relOfCycle X A n z) (relDiffLM_relOfCycle X A n z))
  rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  rw [relKronDesc, h]
  show ((relKronLM X A n (relOfCycle X A n z)).comp ((relChains X A).iCycles n).hom)
      = relKronFunLin X A n z
  rfl

/-- **The relative Kronecker pairing, linear in the cohomological variable.**  It is the factorisation
of `relKronFunLin` through the homology projection, obtained from the *injectivity* of
`LinearMap.lcomp (homologyπ)` (`LinearMap.lcomp_injective_of_surjective`), whose range is exactly the
functionals killing the boundaries. -/
noncomputable def relKronLin (X : TopCat) (A : Set X) (n : ℕ) :
    (relComplex ℤ X A).cycles n →ₗ[ℤ] ((relChains X A).homology n →ₗ[ℤ] ℤ) :=
  let e : ((relChains X A).homology n →ₗ[ℤ] ℤ) ≃ₗ[ℤ]
      LinearMap.range (LinearMap.lcomp (S := ℤ) (N := ℤ) (((relChains X A).homologyπ n).hom)) :=
    LinearEquiv.ofInjective _ (LinearMap.lcomp_injective_of_surjective (S := ℤ) (N := ℤ) _
      ((ModuleCat.epi_iff_surjective ((relChains X A).homologyπ n)).mp inferInstance))
  e.symm.toLinearMap.comp ((relKronFunLin X A n).codRestrict (LinearMap.range _) (fun z =>
    LinearMap.mem_range.mpr ⟨(relKronDesc X A n z).hom, relKronDesc_comp_homologyπ X A n z⟩))

/-- The defining property of `relKronLin`. -/
lemma relKronLin_comp_homologyπ (X : TopCat) (A : Set X) (n : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    (relKronLin X A n z).comp (((relChains X A).homologyπ n).hom) = relKronFunLin X A n z := by
  let e : ((relChains X A).homology n →ₗ[ℤ] ℤ) ≃ₗ[ℤ]
      LinearMap.range (LinearMap.lcomp (S := ℤ) (N := ℤ) (((relChains X A).homologyπ n).hom)) :=
    LinearEquiv.ofInjective _ (LinearMap.lcomp_injective_of_surjective (S := ℤ) (N := ℤ) _
      ((ModuleCat.epi_iff_surjective ((relChains X A).homologyπ n)).mp inferInstance))
  have h := LinearEquiv.apply_symm_apply e
    ((relKronFunLin X A n).codRestrict (LinearMap.range _) (fun z =>
      LinearMap.mem_range.mpr ⟨(relKronDesc X A n z).hom, relKronDesc_comp_homologyπ X A n z⟩) z)
  have h2 := congrArg Subtype.val h
  rw [LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply] at h2
  have h3 : LinearMap.lcomp (S := ℤ) (N := ℤ) (((relChains X A).homologyπ n).hom)
      (relKronLin X A n z) = relKronFunLin X A n z := h2
  rw [LinearMap.lcomp_apply'] at h3
  exact h3

/-- The value of `relKronLin` on the class of a relative cycle. -/
lemma relKronLin_apply (X : TopCat) (A : Set X) (n : ℕ) (z : (relComplex ℤ X A).cycles n)
    (c : (relChains X A).cycles n) :
    relKronLin X A n z (((relChains X A).homologyπ n) c) = relKronFunLin X A n z c := by
  have h := congrArg (fun (g : (relChains X A).cycles n →ₗ[ℤ] ℤ) => g c)
    (relKronLin_comp_homologyπ X A n z)
  simpa only [LinearMap.comp_apply] using h

/-- **A relative coboundary pairs to zero with every relative cycle.** -/
lemma toCycles_relKronLin (X : TopCat) (A : Set X) (n : ℕ) :
    (relComplex ℤ X A).toCycles ((ComplexShape.up ℕ).prev n) n
        ≫ ModuleCat.ofHom (relKronLin X A n) = 0 := by
  generalize hpn : (ComplexShape.up ℕ).prev n = pn
  rcases n with _ | n'
  · have hpn' : pn = 0 := by rw [← hpn]; simp
    rw [hpn']
    rw [HomologicalComplex.toCycles_eq_zero _ (by simp [ComplexShape.up_Rel])]
    simp
  · have hpn' : pn = n' := by rw [← hpn]; simp
    rw [hpn']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : relKronLin X A (n' + 1)
        ((relComplex ℤ X A).toCycles n' (n' + 1) x) = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨cc, rfl⟩ :=
        (ModuleCat.epi_iff_surjective ((relChains X A).homologyπ (n' + 1))).mp inferInstance y
      rw [relKronLin_apply, relKronFunLin_apply]
      have hψ : relOfCycle X A (n' + 1) ((relComplex ℤ X A).toCycles n' (n' + 1) x)
          = relDiffLM ℤ X A n' (show relKern ℤ X A n' from x) := by
        apply Subtype.ext
        simp only [relOfCycle]
        rw [show ((relComplex ℤ X A).iCycles (n' + 1)).hom
              (((relComplex ℤ X A).toCycles n' (n' + 1)) x)
            = ((relComplex ℤ X A).d n' (n' + 1)).hom x from by
          have h := HomologicalComplex.toCycles_i (relComplex ℤ X A) n' (n' + 1)
          have h2 := congrArg (fun (g : (relComplex ℤ X A).X n' ⟶
              (relComplex ℤ X A).X (n' + 1)) => g.hom x) h
          simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2]
        rw [show ((relComplex ℤ X A).d n' (n' + 1)).hom x
            = relDiffLM ℤ X A n' (show relKern ℤ X A n' from x) from by
          rw [relComplex_d]
          rfl]
      rw [hψ]
      obtain ⟨zz, hzz⟩ := relDualProj_surjective X A (n' + 1)
        (((relChains X A).iCycles (n' + 1)) cc)
      rw [← hzz, relKronLM_relDualProj]
      have hcoe := LinearMap.congr_fun
        (relDualDiff_apply_coe X A n' (show relKern ℤ X A n' from x)) zz
      rw [LinearMap.comp_apply] at hcoe
      rw [show (↑(relDiffLM ℤ X A n' (show relKern ℤ X A n' from x)) :
              ↥((singularCochainComplex ℤ X).X (n' + 1)))
            = (relDiff ℤ X A n' (show relKern ℤ X A n' from x)).1 from rfl, hcoe]
      have hker : ((singularChains ℤ X).d (n' + 1) n') zz
          ∈ LinearMap.range ((inclChains X A).f n').hom := by
        rw [← relDualProj_ker X A n']
        rw [LinearMap.mem_ker]
        rw [show (relDualProj X A n') (((singularChains ℤ X).d (n' + 1) n') zz)
            = ((relChains X A).d (n' + 1) n') ((relDualProj X A (n' + 1)) zz) from
          (LinearMap.congr_fun (relDualProj_comm_lm X A n') zz).symm]
        rw [hzz]
        have hcyc : ((relChains X A).d (n' + 1) n')
            (((relChains X A).iCycles (n' + 1)) cc) = 0 := by
          have h := congrArg (fun (g : (relChains X A).cycles (n' + 1) ⟶
              (relChains X A).X n') => g.hom cc)
            (HomologicalComplex.iCycles_d (relChains X A) (n' + 1) n')
          simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
            LinearMap.zero_apply] using h
        rw [hcyc]
      obtain ⟨yy, hyy⟩ := hker
      rw [← hyy]
      exact (relDualKern_iff X A n' (show relKern ℤ X A n' from x).1).1
        (show relKern ℤ X A n' from x).2 yy
    simpa using hx

/-- **The relative Kronecker pairing** `H^n(X,A;ℤ) ⟶ (H_n(X,A;ℤ) →ₗ[ℤ] ℤ)`. -/
noncomputable def relKronMap (X : TopCat) (A : Set X) (n : ℕ) :
    (relComplex ℤ X A).homology n ⟶
      ModuleCat.of ℤ (((relChains X A).homology n) →ₗ[ℤ] ℤ) :=
  descH_K (relComplex ℤ X A) n (ModuleCat.ofHom (relKronLin X A n))
    (toCycles_relKronLin X A n)

/-- The value of `relKronMap` on the class of a relative cocycle. -/
lemma relKronMap_apply (X : TopCat) (A : Set X) (n : ℕ) (z : (relComplex ℤ X A).cycles n) :
    (relKronMap X A n).hom ((relComplex ℤ X A).homologyπ n z) = relKronLin X A n z :=
  descH_apply_K (relComplex ℤ X A) (ModuleCat.ofHom (relKronLin X A n))
    (toCycles_relKronLin X A n) z

/-- **The relative Kronecker pairing exists.** -/
theorem relKronecker_descent (X : TopCat) (A : Set X) (n : ℕ) :
    ∃ kron : relCohomology ℤ X A n →ₗ[ℤ]
        ((relChains X A).homology n →ₗ[ℤ] ℤ),
      ∀ (α : relKern ℤ X A n)
        (hα : relDiffLM ℤ X A n α = 0)
        (cc : (relChains X A).cycles n)
        (zhat : (singularChains ℤ X).X n)
        (hzhat : (CategoryTheory.Limits.cokernel.π
            ((inclChains X A).f n)).hom zhat
          = (relChains_cokernelIso X A n).hom
              ((relChains X A).iCycles n cc)),
        kron (relClassOf ℤ X A α hα)
            ((relChains X A).homologyπ n cc)
          = kronecker ℤ (TopCat.toSSet.obj X) α.1 zhat := by
  refine ⟨(relKronMap X A n).hom, ?_⟩
  intro α hα cc zhat hzhat
  have hclass : relClassOf ℤ X A α hα
      = (relComplex ℤ X A).homologyπ n (relCocycleOf ℤ X A α hα) := rfl
  have hcast : (relChains_cokernelIso X A n).hom ((relDualProj X A n) zhat)
      = (relChains_cokernelIso X A n).hom (((relChains X A).iCycles n) cc) := by
    rw [show (relDualProj X A n) zhat
        = ((CategoryTheory.Limits.cokernel.π (inclChains X A)).f n).hom zhat from rfl]
    rw [relChains_cokernelIso_canon_apply X A n zhat]
    exact hzhat
  have hinj : Function.Injective ((relChains_cokernelIso X A n).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hproj : (relDualProj X A n) zhat = ((relChains X A).iCycles n) cc := hinj hcast
  rw [hclass, relKronMap_apply, relKronLin_apply, relKronFunLin_apply]
  rw [show relOfCycle X A n (relCocycleOf ℤ X A α hα) = α from
    iCycles_relCocycleOf ℤ X A α hα]
  rw [← hproj, relKronLM_relDualProj]
  exact rfl

/-! ## The pairing, packaged -/

/-- **The relative Kronecker pairing** `H^n(X,A;ℤ) →ₗ[ℤ] (H_n(X,A;ℤ) →ₗ[ℤ] ℤ)`, a choice of the
pairing whose existence is `Work.Tubular.relKronecker_descent`.  It is the *relative* counterpart of
`Work.Cohomology.kronH` (which pairs absolute cohomology with absolute homology), and it is what the
mixed cap/cup adjunction of the chapter needs: the cap product of a relative class with a relative
cycle lands in the *absolute* homology of `X`, so it must be paired with the *absolute* cohomology of
`X`, whereas the mixed product is a *relative* class. -/
noncomputable def relKronH (X : TopCat) (A : Set X) (n : ℕ) :
    relCohomology ℤ X A n →ₗ[ℤ] ((relChains X A).homology n →ₗ[ℤ] ℤ) :=
  Classical.choose (relKronecker_descent X A n)

/-- **The computation rule for `relKronH`**: on the class of a relative cocycle `α` and the class of a
relative cycle `cc`, its value is the evaluation of `α` on any absolute chain lifting `cc`. -/
theorem relKronH_apply (X : TopCat) (A : Set X) (n : ℕ)
    (α : relKern ℤ X A n) (hα : relDiffLM ℤ X A n α = 0)
    (cc : (relChains X A).cycles n) (zhat : (singularChains ℤ X).X n)
    (hzhat : (CategoryTheory.Limits.cokernel.π ((inclChains X A).f n)).hom zhat
      = (relChains_cokernelIso X A n).hom ((relChains X A).iCycles n cc)) :
    relKronH X A n (relClassOf ℤ X A α hα) ((relChains X A).homologyπ n cc)
      = kronecker ℤ (TopCat.toSSet.obj X) α.1 zhat :=
  Classical.choose_spec (relKronecker_descent X A n) α hα cc zhat hzhat

end

end Work.Tubular
