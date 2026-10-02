import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.relCupH
import Submission.Work.StemsB.RelCochainDualR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

/-
GUIDANCE FOR THE PROVER (not part of the statement).

This is the ℚ-coefficient form of the *already existing* integral pairing
`Work.Tubular.relKronH` / `Work.Tubular.relKronecker_descent` / `Work.Tubular.relKronH_apply`
(`Submission/Work/Tubular/relKronecker_chain.lean`, over `ℤ` and the `relChains ℤ` model) and of
`Work.Tubular.relKronH_apply_of_relDualProj` (`Submission/Work/Tubular/RelAPI.lean`, which has the
hypothesis in the `relDualProj` form used here).  The requested statement uses the `ℚ`-coefficient
relative chain complex `Work.StemsB.relChainsR ℚ` of `Submission/Work/StemsB/RelChainsR.lean`,
whose degreewise projection is `Work.StemsB.rdRProj` and whose relation to the relative cochains is
`Work.StemsB.relCochainDualR` — the exact `ℚ`-analogue of the ℤ comparison used in
`relKronecker_chain.lean` (there the maps are `relDualProj`/`relDualEquiv` with
`relChains_cokernelIso`).  A direct port of the ℤ argument is expected to work: the ℤ proof descends
the evaluation `relKronLin` through the cycles and the cohomology of `relComplex` (`descH_K`), and
the two descent conditions are exactly `rdRKern_iff`/`rdRProj_ker` (varying the lift) and the
Leibniz rule for the differential `relDiffLM` (varying the representative).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

noncomputable section

open Work.Cohomology

variable (R : Type) [CommRing R] (X : TopCat) (A : Set X)

/-! ## The coefficient-generic relative Kronecker pairing

This is the port of `Work.Tubular.relKronecker_descent` from the `ℤ`-coefficient model
`Work.Cohomology.relChains` to the coefficient-generic relative chains `Work.StemsB.relChainsR R`
of `Submission/Work/StemsB/RelChainsR.lean`, whose degreewise projection is
`Work.StemsB.rdRProj` and whose degreewise duality with the relative cochains is
`Work.StemsB.rdREquiv` (`Submission/Work/StemsB/RelCochainDualR.lean`).  Every step of the integral
argument only uses the general lemmas of that file, so it carries over verbatim. -/

/-- The functional on the relative chains associated with a relative cochain: the inverse of the
degreewise isomorphism `Work.StemsB.rdREquiv`. -/
def relKronLMR (n : ℕ) :
    relKern R X A n →ₗ[R] ((Work.StemsB.relChainsR R X A).X n →ₗ[R] R) :=
  (Work.StemsB.rdREquiv R X A n).symm

/-- The value of `relKronLMR` on the image of a lift. -/
theorem relKronLMR_rdRProj (n : ℕ) (φ : relKern R X A n)
    (x : (singularChains R X).X n) :
    relKronLMR R X A n φ ((Work.StemsB.rdRProj R X A n) x) = Work.StemsB.rdRLM R X n φ.1 x := by
  have h := LinearMap.congr_fun (Work.StemsB.rdREquiv_symm_comp R X A n φ) x
  rw [LinearMap.comp_apply] at h
  exact h

/-- The chain-level relative pairing of a relative cochain with the cycles of the relative
chains. -/
def relKronCycEvalR (n : ℕ) (φ : relKern R X A n) :
    (Work.StemsB.relChainsR R X A).cycles n →ₗ[R] R :=
  (relKronLMR R X A n φ).comp ((Work.StemsB.relChainsR R X A).iCycles n).hom

/-- The `iCycles` of the boundary is the differential. -/
lemma iCycles_toCycles_relChainsR (i j : ℕ)
    (y : (Work.StemsB.relChainsR R X A).X i) :
    ((Work.StemsB.relChainsR R X A).iCycles j).hom
        (((Work.StemsB.relChainsR R X A).toCycles i j) y)
      = ((Work.StemsB.relChainsR R X A).d i j).hom y := by
  have h := congrArg (fun (g : (Work.StemsB.relChainsR R X A).X i ⟶
      (Work.StemsB.relChainsR R X A).X j) => g.hom y)
    (HomologicalComplex.toCycles_i (Work.StemsB.relChainsR R X A) i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- **A relative cocycle pairs to zero with a relative boundary**: the descent in the chain
variable. -/
lemma toCycles_relKronCycEvalR (n : ℕ) (φ : relKern R X A n)
    (hφ : relDiffLM R X A n φ = 0) :
    (Work.StemsB.relChainsR R X A).toCycles (n + 1) n
        ≫ ModuleCat.ofHom (relKronCycEvalR R X A n φ) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  show relKronCycEvalR R X A n φ (((Work.StemsB.relChainsR R X A).toCycles (n + 1) n) y) = 0
  rw [relKronCycEvalR, LinearMap.comp_apply, iCycles_toCycles_relChainsR]
  obtain ⟨ŷ, hŷ⟩ := Work.StemsB.rdRProj_surjective R X A (n + 1) y
  rw [← hŷ]
  have hcomm : ((Work.StemsB.relChainsR R X A).d (n + 1) n)
        ((Work.StemsB.rdRProj R X A (n + 1)) ŷ)
      = (Work.StemsB.rdRProj R X A n) (((singularChains R X).d (n + 1) n) ŷ) :=
    LinearMap.congr_fun (Work.StemsB.rdRProj_comm_lm R X A n) ŷ
  rw [hcomm, relKronLMR_rdRProj, ← Work.StemsB.rdRDiff_apply R X A n φ ŷ]
  have h2 : (relDiff R X A n φ).1 = 0 := by
    rw [show (relDiff R X A n φ : relKern R X A (n + 1)) = relDiffLM R X A n φ from rfl, hφ]
    simp
  rw [h2]
  simp [Work.StemsB.rdRLM]

/-- **Descent in the chain variable.**  The functional on the relative cycles given by a relative
*cocycle* factors through the relative homology. -/
noncomputable def relKronCocycDescR (n : ℕ) (φ : relKern R X A n)
    (hφ : relDiffLM R X A n φ = 0) :
    (Work.StemsB.relChainsR R X A).homology n ⟶ ModuleCat.of R R :=
  ((Work.StemsB.relChainsR R X A).homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n)).desc
    (CokernelCofork.ofπ (ModuleCat.ofHom (relKronCycEvalR R X A n φ))
      (toCycles_relKronCycEvalR R X A n φ hφ))

/-- Computation rule for `relKronCocycDescR`. -/
lemma homologyπ_relKronCocycDescR (n : ℕ) (φ : relKern R X A n)
    (hφ : relDiffLM R X A n φ = 0) :
    (Work.StemsB.relChainsR R X A).homologyπ n ≫ relKronCocycDescR R X A n φ hφ
      = ModuleCat.ofHom (relKronCycEvalR R X A n φ) :=
  Cofork.IsColimit.π_desc
    (s := CokernelCofork.ofπ ((Work.StemsB.relChainsR R X A).homologyπ n)
      (HomologicalComplex.toCycles_comp_homologyπ (Work.StemsB.relChainsR R X A) (n + 1) n))
    (t := CokernelCofork.ofπ (ModuleCat.ofHom (relKronCycEvalR R X A n φ))
      (toCycles_relKronCycEvalR R X A n φ hφ))
    (((Work.StemsB.relChainsR R X A).homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n)))

/-- Computation rule for `relKronCocycDescR` on the class of a relative cycle. -/
lemma relKronCocycDescR_apply (n : ℕ) (φ : relKern R X A n)
    (hφ : relDiffLM R X A n φ = 0) (c : (Work.StemsB.relChainsR R X A).cycles n) :
    (relKronCocycDescR R X A n φ hφ).hom
        (((Work.StemsB.relChainsR R X A).homologyπ n) c)
      = relKronLMR R X A n φ (((Work.StemsB.relChainsR R X A).iCycles n) c) := by
  have h := congrArg (fun (g : (Work.StemsB.relChainsR R X A).cycles n ⟶ ModuleCat.of R R) =>
      g.hom c) (homologyπ_relKronCocycDescR R X A n φ hφ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    relKronCycEvalR, LinearMap.comp_apply] at h
  exact h

/-! ## The pairing of a relative cocycle with the relative homology -/

/-- The relative cochain underlying a cycle of the relative cochain complex. -/
def relOfCycleR (n : ℕ) (z : (relComplex R X A).cycles n) : relKern R X A n :=
  ((relComplex R X A).iCycles n).hom z

/-- A relative cocycle is a cocycle for the relative differential. -/
lemma relDiffLM_iCyclesR (n : ℕ) (z : (relComplex R X A).cycles n) :
    relDiffLM R X A n (((relComplex R X A).iCycles n).hom z) = 0 := by
  have h := congrArg
    (fun (g : (relComplex R X A).cycles n ⟶ (relComplex R X A).X (n + 1)) => g.hom z)
    (HomologicalComplex.iCycles_d (relComplex R X A) n (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  rw [relComplex_d] at h
  exact h

/-- A cycle of the relative cochain complex is a relative cocycle. -/
lemma relDiffLM_relOfCycleR (n : ℕ) (z : (relComplex R X A).cycles n) :
    relDiffLM R X A n (relOfCycleR R X A n z) = 0 :=
  relDiffLM_iCyclesR R X A n z

/-- The relative cochain underlying a relative cycle, as a linear map in the cycle. -/
noncomputable def relOfCycleLinR (n : ℕ) :
    (relComplex R X A).cycles n →ₗ[R] relKern R X A n :=
  ((relComplex R X A).iCycles n).hom

/-- The functional on the relative cycles associated with a relative cochain, as a linear map. -/
noncomputable def relKronCycEvalLinR (n : ℕ) :
    relKern R X A n →ₗ[R] ((Work.StemsB.relChainsR R X A).cycles n →ₗ[R] R) :=
  (LinearMap.lcomp (S := R) (N := R) ((Work.StemsB.relChainsR R X A).iCycles n).hom).comp
    (relKronLMR R X A n)

/-- The pairing on the cycles, linear in *both* variables (no `map_smul'` is proved by hand: it is a
composite of existing `LinearMap`s). -/
noncomputable def relKronFunLinR (n : ℕ) :
    (relComplex R X A).cycles n →ₗ[R] ((Work.StemsB.relChainsR R X A).cycles n →ₗ[R] R) :=
  (relKronCycEvalLinR R X A n).comp (relOfCycleLinR R X A n)

/-- The computation rule for `relKronFunLinR`. -/
lemma relKronFunLinR_apply (n : ℕ)
    (z : (relComplex R X A).cycles n) (c : (Work.StemsB.relChainsR R X A).cycles n) :
    relKronFunLinR R X A n z c
      = relKronLMR R X A n (relOfCycleR R X A n z)
          (((Work.StemsB.relChainsR R X A).iCycles n) c) := by
  show ((relKronLMR R X A n (relOfCycleR R X A n z)).comp
      ((Work.StemsB.relChainsR R X A).iCycles n).hom) c
      = relKronLMR R X A n (relOfCycleR R X A n z)
          (((Work.StemsB.relChainsR R X A).iCycles n) c)
  rfl

/-- The factorisation of the functional of a relative cycle through the homology of the relative
chains: the descent in the *chain* variable, applied to the relative cocycle of the relative
cycle. -/
noncomputable def relKronDescR (n : ℕ) (z : (relComplex R X A).cycles n) :
    (Work.StemsB.relChainsR R X A).homology n ⟶ ModuleCat.of R R :=
  relKronCocycDescR R X A n (relOfCycleR R X A n z) (relDiffLM_relOfCycleR R X A n z)

/-- The defining property of `relKronDescR`: composed with the homology projection it is
`relKronFunLinR`. -/
lemma relKronDescR_comp_homologyπ (n : ℕ) (z : (relComplex R X A).cycles n) :
    (relKronDescR R X A n z).hom.comp (((Work.StemsB.relChainsR R X A).homologyπ n).hom)
      = relKronFunLinR R X A n z := by
  have h := congrArg ModuleCat.Hom.hom
    (homologyπ_relKronCocycDescR R X A n (relOfCycleR R X A n z)
      (relDiffLM_relOfCycleR R X A n z))
  rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  rw [relKronDescR, h]
  show ((relKronLMR R X A n (relOfCycleR R X A n z)).comp
      ((Work.StemsB.relChainsR R X A).iCycles n).hom) = relKronFunLinR R X A n z
  rfl

/-- **The relative Kronecker pairing, linear in the cohomological variable.**  It is the
factorisation of `relKronFunLinR` through the homology projection, obtained from the *injectivity*
of `LinearMap.lcomp (homologyπ)` (`LinearMap.lcomp_injective_of_surjective`), whose range is exactly
the functionals killing the boundaries. -/
noncomputable def relKronLinR (n : ℕ) :
    (relComplex R X A).cycles n →ₗ[R] ((Work.StemsB.relChainsR R X A).homology n →ₗ[R] R) :=
  let e : ((Work.StemsB.relChainsR R X A).homology n →ₗ[R] R) ≃ₗ[R]
      LinearMap.range (LinearMap.lcomp (S := R) (N := R)
        (((Work.StemsB.relChainsR R X A).homologyπ n).hom)) :=
    LinearEquiv.ofInjective _ (LinearMap.lcomp_injective_of_surjective (S := R) (N := R) _
      ((ModuleCat.epi_iff_surjective ((Work.StemsB.relChainsR R X A).homologyπ n)).mp
        inferInstance))
  e.symm.toLinearMap.comp ((relKronFunLinR R X A n).codRestrict (LinearMap.range _) (fun z =>
    LinearMap.mem_range.mpr ⟨(relKronDescR R X A n z).hom,
      relKronDescR_comp_homologyπ R X A n z⟩))

/-- The defining property of `relKronLinR`. -/
lemma relKronLinR_comp_homologyπ (n : ℕ) (z : (relComplex R X A).cycles n) :
    (relKronLinR R X A n z).comp (((Work.StemsB.relChainsR R X A).homologyπ n).hom)
      = relKronFunLinR R X A n z := by
  let e : ((Work.StemsB.relChainsR R X A).homology n →ₗ[R] R) ≃ₗ[R]
      LinearMap.range (LinearMap.lcomp (S := R) (N := R)
        (((Work.StemsB.relChainsR R X A).homologyπ n).hom)) :=
    LinearEquiv.ofInjective _ (LinearMap.lcomp_injective_of_surjective (S := R) (N := R) _
      ((ModuleCat.epi_iff_surjective ((Work.StemsB.relChainsR R X A).homologyπ n)).mp
        inferInstance))
  have h := LinearEquiv.apply_symm_apply e
    ((relKronFunLinR R X A n).codRestrict (LinearMap.range _) (fun z =>
      LinearMap.mem_range.mpr ⟨(relKronDescR R X A n z).hom,
        relKronDescR_comp_homologyπ R X A n z⟩) z)
  have h2 := congrArg Subtype.val h
  rw [LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply] at h2
  have h3 : LinearMap.lcomp (S := R) (N := R)
      (((Work.StemsB.relChainsR R X A).homologyπ n).hom) (relKronLinR R X A n z)
      = relKronFunLinR R X A n z := h2
  rw [LinearMap.lcomp_apply'] at h3
  exact h3

/-- The value of `relKronLinR` on the class of a relative cycle. -/
lemma relKronLinR_apply (n : ℕ) (z : (relComplex R X A).cycles n)
    (c : (Work.StemsB.relChainsR R X A).cycles n) :
    relKronLinR R X A n z (((Work.StemsB.relChainsR R X A).homologyπ n) c)
      = relKronFunLinR R X A n z c := by
  have h := congrArg (fun (g : (Work.StemsB.relChainsR R X A).cycles n →ₗ[R] R) => g c)
    (relKronLinR_comp_homologyπ R X A n z)
  simpa only [LinearMap.comp_apply] using h

/-- **A relative coboundary pairs to zero with every relative cycle.** -/
lemma toCycles_relKronLinR (n : ℕ) :
    (relComplex R X A).toCycles ((ComplexShape.up ℕ).prev n) n
        ≫ ModuleCat.ofHom (relKronLinR R X A n) = 0 := by
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
    have hx : relKronLinR R X A (n' + 1)
        ((relComplex R X A).toCycles n' (n' + 1) x) = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨cc, rfl⟩ :=
        (ModuleCat.epi_iff_surjective ((Work.StemsB.relChainsR R X A).homologyπ (n' + 1))).mp
          inferInstance y
      rw [relKronLinR_apply, relKronFunLinR_apply]
      have hψ : relOfCycleR R X A (n' + 1)
          ((relComplex R X A).toCycles n' (n' + 1) x)
          = relDiffLM R X A n' (show relKern R X A n' from x) := by
        apply Subtype.ext
        simp only [relOfCycleR]
        rw [show ((relComplex R X A).iCycles (n' + 1)).hom
              (((relComplex R X A).toCycles n' (n' + 1)) x)
            = ((relComplex R X A).d n' (n' + 1)).hom x from by
          have h := HomologicalComplex.toCycles_i (relComplex R X A) n' (n' + 1)
          have h2 := congrArg (fun (g : (relComplex R X A).X n' ⟶
              (relComplex R X A).X (n' + 1)) => g.hom x) h
          simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2]
        rw [show ((relComplex R X A).d n' (n' + 1)).hom x
            = relDiffLM R X A n' (show relKern R X A n' from x) from by
          rw [relComplex_d]
          rfl]
      rw [hψ]
      obtain ⟨zz, hzz⟩ := Work.StemsB.rdRProj_surjective R X A (n' + 1)
        (((Work.StemsB.relChainsR R X A).iCycles (n' + 1)) cc)
      rw [← hzz, relKronLMR_rdRProj]
      have hcoe := LinearMap.congr_fun
        (Work.StemsB.rdRDiff_apply_coe R X A n' (show relKern R X A n' from x)) zz
      rw [LinearMap.comp_apply] at hcoe
      rw [show (↑(relDiffLM R X A n' (show relKern R X A n' from x)) :
              ↥((singularCochainComplex R X).X (n' + 1)))
            = (relDiff R X A n' (show relKern R X A n' from x)).1 from rfl, hcoe]
      have hker : ((singularChains R X).d (n' + 1) n') zz
          ∈ LinearMap.range ((Work.StemsB.relChainsRIncl R X A).f n').hom := by
        rw [← Work.StemsB.rdRProj_ker R X A n']
        rw [LinearMap.mem_ker]
        rw [show (Work.StemsB.rdRProj R X A n')
              (((singularChains R X).d (n' + 1) n') zz)
            = ((Work.StemsB.relChainsR R X A).d (n' + 1) n')
                ((Work.StemsB.rdRProj R X A (n' + 1)) zz) from
          (LinearMap.congr_fun (Work.StemsB.rdRProj_comm_lm R X A n') zz).symm]
        rw [hzz]
        have hcyc : ((Work.StemsB.relChainsR R X A).d (n' + 1) n')
            (((Work.StemsB.relChainsR R X A).iCycles (n' + 1)) cc) = 0 := by
          have h := congrArg (fun (g : (Work.StemsB.relChainsR R X A).cycles (n' + 1) ⟶
              (Work.StemsB.relChainsR R X A).X n') => g.hom cc)
            (HomologicalComplex.iCycles_d (Work.StemsB.relChainsR R X A) (n' + 1) n')
          simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
            LinearMap.zero_apply] using h
        rw [hcyc]
      obtain ⟨yy, hyy⟩ := hker
      rw [← hyy]
      exact (Work.StemsB.rdRKern_iff R X A n' (show relKern R X A n' from x).1).1
        (show relKern R X A n' from x).2 yy
    simpa using hx

/-- **The relative Kronecker pairing** `H^n(X,A;R) ⟶ (H_n(X,A;R) →ₗ[R] R)`. -/
noncomputable def relKronMapR (n : ℕ) :
    (relComplex R X A).homology n ⟶
      ModuleCat.of R (((Work.StemsB.relChainsR R X A).homology n) →ₗ[R] R) :=
  descH_K (relComplex R X A) n (ModuleCat.ofHom (relKronLinR R X A n))
    (toCycles_relKronLinR R X A n)

/-- The value of `relKronMapR` on the class of a relative cocycle. -/
lemma relKronMapR_apply (n : ℕ) (z : (relComplex R X A).cycles n) :
    (relKronMapR R X A n).hom ((relComplex R X A).homologyπ n z)
      = relKronLinR R X A n z :=
  descH_apply_K (relComplex R X A) (ModuleCat.ofHom (relKronLinR R X A n))
    (toCycles_relKronLinR R X A n) z

/-- **The relative Kronecker pairing exists**, coefficient-generically.  The `ℚ`-coefficient
statement `Work.Serre.relKron_exists` is the case `R = ℚ`. -/
theorem relKronecker_descent_R (n : ℕ) :
    ∃ e : ↥((relComplex R X A).homology n) →ₗ[R]
        (↥((Work.StemsB.relChainsR R X A).homology n) →ₗ[R] R),
      ∀ (φ : relKern R X A n)
        (hφ : relDiffLM R X A n φ = 0)
        (c : (Work.StemsB.relChainsR R X A).cycles n)
        (x : (singularChains R X).X n)
        (hx : (Work.StemsB.rdRProj R X A n) x
          = (Work.StemsB.relChainsR R X A).iCycles n c),
        e (relClassOf R X A φ hφ)
          ((Work.StemsB.relChainsR R X A).homologyπ n c)
            = Work.StemsB.rdRLM R X n φ.1 x := by
  refine ⟨(relKronMapR R X A n).hom, ?_⟩
  intro φ hφ c x hx
  have hclass : relClassOf R X A φ hφ
      = (relComplex R X A).homologyπ n (relCocycleOf R X A φ hφ) := rfl
  rw [hclass, relKronMapR_apply, relKronLinR_apply, relKronFunLinR_apply]
  rw [show relOfCycleR R X A n (relCocycleOf R X A φ hφ) = φ from
    iCycles_relCocycleOf R X A φ hφ]
  rw [← hx, relKronLMR_rdRProj]

end

theorem relKron_exists (X : TopCat) (A : Set X) (n : ℕ) :
    ∃ e : ↥((Work.Cohomology.relComplex ℚ X A).homology n) →ₗ[ℚ]
        (↥((Work.StemsB.relChainsR ℚ X A).homology n) →ₗ[ℚ] ℚ),
      ∀ (φ : Work.Cohomology.relKern ℚ X A n)
        (hφ : Work.Cohomology.relDiffLM ℚ X A n φ = 0)
        (c : (Work.StemsB.relChainsR ℚ X A).cycles n)
        (x : (Work.Cohomology.singularChains ℚ X).X n)
        (hx : (Work.StemsB.rdRProj ℚ X A n) x = (Work.StemsB.relChainsR ℚ X A).iCycles n c),
        e (Work.Cohomology.relClassOf ℚ X A φ hφ)
          ((Work.StemsB.relChainsR ℚ X A).homologyπ n c)
            = Work.StemsB.rdRLM ℚ X n φ.1 x :=
  relKronecker_descent_R ℚ X A n

end Work.Serre
