import Mathlib
import Submission.Work.Serre.relKron_exists
import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.StemsB.CollarRat
import Submission.Work.Cohomology.relCapHHom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative Kronecker pairing over `ℚ` is an isomorphism

`Work.Serre.relKron_exists` constructs the relative Kronecker pairing
`relKronMapR ℚ X A n : H^n(X,A;ℚ) → (H_n(X,A;ℚ) →ₗ[ℚ] ℚ)` together with its computation rule
(`relClassOf φ` paired with `homologyπ c` is `φ(x)` for any lift `x` of the cycle `c`).

Over a *field* the pairing is an isomorphism (the universal coefficient theorem needs no
finiteness or freeness hypothesis: every subspace of a `ℚ`-vector space is a direct summand).  This
file proves that, so that `relKronMapR ℚ X A n` is a linear equivalence, as requested by
`Work.Serre.relKronEquiv`.

The two halves are:

* `relKronMapRSurjective` — every functional on `H_n(X,A;ℚ)` is the evaluation on some cohomology
  class: a functional on the cycles extends to the chains (`Subspace.dualLift`), and the extension
  is a cocycle because it vanishes on boundaries (they are cycles, hence `homologyπ` kills them);
* `relKronMapRInjective` — a cocycle whose functional vanishes on the cycles is a coboundary:
  by `LinearMap.range_dualMap_eq_dualAnnihilator_ker` it factors through the differential, hence is
  the coboundary of a relative cochain.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## The cycles of the rational relative chains, concretely -/

/-- The abstract `n`-cycles of the relative singular chains with `ℚ` coefficients, identified with
the concrete kernel of the differential `dₙ : C_n(X,A;ℚ) → C_{n-1}(X,A;ℚ)`. -/
noncomputable def relChainsCycIso (X : TopCat) (A : Set X) (n : ℕ) :
    (Work.StemsB.relChainsR ℚ X A).cycles n ≅
      ModuleCat.of ℚ ↥(LinearMap.ker (((Work.StemsB.relChainsR ℚ X A).d n (n - 1)).hom)) :=
  ((Work.StemsB.relChainsR ℚ X A).cyclesIsoSc' (n + 1) n (n - 1)
      (Work.Cohomology.down_prev n) (Work.Cohomology.down_next n)) ≪≫
    ShortComplex.moduleCatCyclesIso ((Work.StemsB.relChainsR ℚ X A).sc' (n + 1) n (n - 1))

/-- The inclusion of the cycles is the inclusion of the concrete kernel. -/
lemma relChainsCycIso_hom_i (X : TopCat) (A : Set X) (n : ℕ) :
    (relChainsCycIso X A n).hom ≫
        (ShortComplex.moduleCatLeftHomologyData
          ((Work.StemsB.relChainsR ℚ X A).sc' (n + 1) n (n - 1))).i
      = (Work.StemsB.relChainsR ℚ X A).iCycles n := by
  rw [relChainsCycIso, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- `relChainsCycIso` does not change the underlying element. -/
lemma relChainsCycIso_hom_val (X : TopCat) (A : Set X) (n : ℕ)
    (c : (Work.StemsB.relChainsR ℚ X A).cycles n) :
    ((relChainsCycIso X A n).hom c : ↥((Work.StemsB.relChainsR ℚ X A).X n))
      = ((Work.StemsB.relChainsR ℚ X A).iCycles n).hom c := by
  have h := congrArg (fun (m : (Work.StemsB.relChainsR ℚ X A).cycles n ⟶
      (Work.StemsB.relChainsR ℚ X A).X n) => ModuleCat.Hom.hom m c)
    (relChainsCycIso_hom_i X A n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The inverse of `relChainsCycIso`, evaluated on an element of the concrete kernel, is a cycle
with the same underlying chain. -/
lemma relChainsCycIso_symm_val (X : TopCat) (A : Set X) (n : ℕ)
    (z : ↥(LinearMap.ker (((Work.StemsB.relChainsR ℚ X A).d n (n - 1)).hom))) :
    ((Work.StemsB.relChainsR ℚ X A).iCycles n) (((relChainsCycIso X A n).toLinearEquiv).symm z)
      = (z : ↥((Work.StemsB.relChainsR ℚ X A).X n)) := by
  have h2 := relChainsCycIso_hom_val X A n (((relChainsCycIso X A n).toLinearEquiv).symm z)
  rw [show (relChainsCycIso X A n).hom (((relChainsCycIso X A n).toLinearEquiv).symm z) = z from
    ((relChainsCycIso X A n).toLinearEquiv).apply_symm_apply z] at h2
  exact h2.symm

/-- The `(rdREquiv).symm`-image of the coboundary of `rdREquiv g` is `g` composed with the
differential of the relative chains. -/
lemma rdREquiv_symm_relDiffLM (X : TopCat) (A : Set X) (n : ℕ)
    (g : ↥((Work.StemsB.relChainsR ℚ X A).X n) →ₗ[ℚ] ℚ) :
    (Work.StemsB.rdREquiv ℚ X A (n + 1)).symm
        (Work.Cohomology.relDiffLM ℚ X A n (Work.StemsB.rdREquiv ℚ X A n g))
      = g.comp (((Work.StemsB.relChainsR ℚ X A).d (n + 1) n)).hom := by
  ext w
  obtain ⟨x, rfl⟩ := Work.StemsB.rdRProj_surjective ℚ X A (n + 1) w
  have hcomp := LinearMap.congr_fun (Work.StemsB.rdREquiv_symm_comp ℚ X A (n + 1)
    (Work.Cohomology.relDiffLM ℚ X A n (Work.StemsB.rdREquiv ℚ X A n g))) x
  rw [LinearMap.comp_apply] at hcomp
  rw [hcomp]
  rw [show (Work.Cohomology.relDiffLM ℚ X A n (Work.StemsB.rdREquiv ℚ X A n g)).1
      = (Work.Cohomology.relDiff ℚ X A n (Work.StemsB.rdREquiv ℚ X A n g)).1 from rfl]
  rw [Work.StemsB.rdRDiff_apply_coe]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [show (Work.StemsB.rdRLM ℚ X n (Work.StemsB.rdREquiv ℚ X A n g).1)
      = g.comp (Work.StemsB.rdRProj ℚ X A n).hom from
    Work.StemsB.rdREquiv_apply_coe ℚ X A n g]
  rw [LinearMap.comp_apply]
  rw [show ((Work.StemsB.rdRProj ℚ X A n).hom)
        (((Work.Cohomology.singularChains ℚ X).d (n + 1) n) x)
      = ((Work.StemsB.relChainsR ℚ X A).d (n + 1) n)
        ((Work.StemsB.rdRProj ℚ X A (n + 1)) x) from
    (LinearMap.congr_fun (Work.StemsB.rdRProj_comm_lm ℚ X A n) x).symm]

/-! ## Surjectivity of the pairing -/

/-- **Every functional on the relative homology is the evaluation on a relative cohomology
class.** -/
theorem relKronMapRSurjective (X : TopCat) (A : Set X) (n : ℕ) :
    Function.Surjective ((relKronMapR ℚ X A n).hom) := by
  intro g
  set Z : Submodule ℚ ↥((Work.StemsB.relChainsR ℚ X A).X n) :=
    LinearMap.ker (((Work.StemsB.relChainsR ℚ X A).d n (n - 1)).hom) with hZ
  let cycInv : ↥Z →ₗ[ℚ] ↥((Work.StemsB.relChainsR ℚ X A).cycles n) :=
    (relChainsCycIso X A n).toLinearEquiv.symm
  let ψ : Z →ₗ[ℚ] ℚ :=
    (g.comp (((Work.StemsB.relChainsR ℚ X A).homologyπ n).hom)).comp cycInv
  let α : ↥((Work.StemsB.relChainsR ℚ X A).X n) →ₗ[ℚ] ℚ := Subspace.dualLift Z ψ
  have hαval : ∀ (x : ↥((Work.StemsB.relChainsR ℚ X A).X n)) (hx : x ∈ Z),
      α x = ψ ⟨x, hx⟩ := fun x hx => Subspace.dualLift_of_mem hx
  have hψval : ∀ z : ↥Z,
      ψ z = g (((Work.StemsB.relChainsR ℚ X A).homologyπ n).hom (cycInv z)) := fun z => rfl
  have hcyc : ∀ z : ↥Z,
      ((Work.StemsB.relChainsR ℚ X A).iCycles n) (cycInv z)
        = (z : ↥((Work.StemsB.relChainsR ℚ X A).X n)) :=
    fun z => relChainsCycIso_symm_val X A n z
  -- `α` vanishes on boundaries: they are cycles, hence die in homology
  have hα0 : ∀ y : ↥((Work.StemsB.relChainsR ℚ X A).X (n + 1)),
      α (((Work.StemsB.relChainsR ℚ X A).d (n + 1) n).hom y) = 0 := by
    intro y
    have hdy : ((Work.StemsB.relChainsR ℚ X A).d (n + 1) n).hom y ∈ Z := by
      rw [hZ, LinearMap.mem_ker]
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.d_comp_d (Work.StemsB.relChainsR ℚ X A) (n + 1) n (n - 1))
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h y
    rw [hαval _ hdy, hψval]
    rw [Work.Cohomology.homologyπ_eq_zero_of_iCycles_eq_d ℚ (Work.StemsB.relChainsR ℚ X A) n _
      y (hcyc ⟨_, hdy⟩), map_zero]
  -- the relative cochain attached to `α`
  let φ : Work.Cohomology.relKern ℚ X A n := (Work.StemsB.rdREquiv ℚ X A n) α
  have hφ : Work.Cohomology.relDiffLM ℚ X A n φ = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    show (Work.StemsB.rdRLM ℚ X (n + 1)
      (↑(Work.Cohomology.relDiff ℚ X A n φ) :
        ↥((Work.Cohomology.singularCochainComplex ℚ X).X (n + 1)))) x = 0
    rw [Work.StemsB.rdRDiff_apply]
    rw [show φ.1 = ((Work.StemsB.rdREquiv ℚ X A n) α).1 from rfl,
      Work.StemsB.rdREquiv_apply_coe, LinearMap.comp_apply]
    rw [show ((Work.StemsB.rdRProj ℚ X A n).hom)
          (((Work.Cohomology.singularChains ℚ X).d (n + 1) n) x)
        = ((Work.StemsB.relChainsR ℚ X A).d (n + 1) n)
          ((Work.StemsB.rdRProj ℚ X A (n + 1)) x) from
      (LinearMap.congr_fun (Work.StemsB.rdRProj_comm_lm ℚ X A n) x).symm]
    exact hα0 _
  refine ⟨Work.Cohomology.relClassOf ℚ X A φ hφ, ?_⟩
  refine LinearMap.ext fun c => ?_
  obtain ⟨cc, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((Work.StemsB.relChainsR ℚ X A).homologyπ n)).mp inferInstance c
  have hclass : Work.Cohomology.relClassOf ℚ X A φ hφ
      = ((Work.Cohomology.relComplex ℚ X A).homologyπ n)
        (Work.Cohomology.relCocycleOf ℚ X A φ hφ) := rfl
  rw [hclass, relKronMapR_apply, relKronLinR_apply, relKronFunLinR_apply]
  rw [show relOfCycleR ℚ X A n (Work.Cohomology.relCocycleOf ℚ X A φ hφ) = φ from
    Work.Cohomology.iCycles_relCocycleOf ℚ X A φ hφ]
  have hαφ : (relKronLMR ℚ X A n) φ = α := by
    show (Work.StemsB.rdREquiv ℚ X A n).symm ((Work.StemsB.rdREquiv ℚ X A n) α) = α
    exact LinearEquiv.symm_apply_apply _ _
  have hcycl : ((Work.StemsB.relChainsR ℚ X A).iCycles n) cc ∈ Z := by
    rw [hZ, LinearMap.mem_ker]
    have h := congrArg (fun (m : (Work.StemsB.relChainsR ℚ X A).cycles n ⟶
        (Work.StemsB.relChainsR ℚ X A).X (n - 1)) => ModuleCat.Hom.hom m cc)
      (HomologicalComplex.iCycles_d (Work.StemsB.relChainsR ℚ X A) n (n - 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hz : cycInv ⟨((Work.StemsB.relChainsR ℚ X A).iCycles n) cc, hcycl⟩ = cc := by
    apply Work.Cohomology.iCycles_injective_C ℚ (Work.StemsB.relChainsR ℚ X A) n
    rw [hcyc ⟨_, hcycl⟩]
  rw [hαφ, hαval _ hcycl, hψval, hz]

/-! ## Injectivity of the pairing -/

/-- **A relative cocycle whose functional vanishes on all relative cycles is a coboundary.**  The
functional `(rdREquiv).symm φ` of a relative cocycle `φ` vanishes on the cycles, hence (over a
field, `LinearMap.range_dualMap_eq_dualAnnihilator_ker`) factors through the differential, and the
resulting cochain has `φ` as its coboundary. -/
theorem relKronMapRInjective (X : TopCat) (A : Set X) (n : ℕ) :
    Function.Injective ((relKronMapR ℚ X A n).hom) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro u hu
  rw [LinearMap.mem_ker] at hu
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.relComplex ℚ X A).homologyπ n)).mp inferInstance u
  set Z : Submodule ℚ ↥((Work.StemsB.relChainsR ℚ X A).X n) :=
    LinearMap.ker (((Work.StemsB.relChainsR ℚ X A).d n (n - 1)).hom) with hZ
  -- the functional of the cocycle `i z` vanishes on the (abstract) cycles
  have hA : ∀ c : (Work.StemsB.relChainsR ℚ X A).cycles n,
      ((Work.StemsB.rdREquiv ℚ X A n).symm
          (((Work.Cohomology.relComplex ℚ X A).iCycles n).hom z))
        (((Work.StemsB.relChainsR ℚ X A).iCycles n) c) = 0 := by
    intro c
    have h : (relKronMapR ℚ X A n).hom (((Work.Cohomology.relComplex ℚ X A).homologyπ n) z)
        (((Work.StemsB.relChainsR ℚ X A).homologyπ n) c) = 0 := by
      rw [hu, LinearMap.zero_apply]
    rw [relKronMapR_apply ℚ X A n z, relKronLinR_apply ℚ X A n z c,
      relKronFunLinR_apply ℚ X A n z c] at h
    exact h
  -- hence it vanishes on the concrete kernel of the differential
  have hvan : ∀ x ∈ LinearMap.ker (((Work.StemsB.relChainsR ℚ X A).d n (n - 1)).hom),
      ((Work.StemsB.rdREquiv ℚ X A n).symm
        (((Work.Cohomology.relComplex ℚ X A).iCycles n).hom z)) x = 0 := by
    intro x hx
    have hx' : ((Work.StemsB.relChainsR ℚ X A).iCycles n)
        ((relChainsCycIso X A n).toLinearEquiv.symm ⟨x, hx⟩) = x :=
      relChainsCycIso_symm_val X A n ⟨x, hx⟩
    rw [← hx']
    exact hA _
  -- so it factors through the differential
  obtain ⟨g₀, hg₀⟩ := LinearMap.mem_range.mp (show
      ((Work.StemsB.rdREquiv ℚ X A n).symm
        (((Work.Cohomology.relComplex ℚ X A).iCycles n).hom z)) ∈
        LinearMap.range (((Work.StemsB.relChainsR ℚ X A).d n (n - 1)).hom).dualMap from by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    exact hvan)
  have hg₀' : g₀.comp (((Work.StemsB.relChainsR ℚ X A).d n (n - 1)).hom)
      = ((Work.StemsB.rdREquiv ℚ X A n).symm
        (((Work.Cohomology.relComplex ℚ X A).iCycles n).hom z)) := by
    rw [← LinearMap.dualMap_apply']
    exact hg₀
  rcases n with _ | m
  · -- degree `0`: the differential out of degree `0` vanishes, so the functional is zero
    have hker : LinearMap.ker (((Work.StemsB.relChainsR ℚ X A).d 0 (0 - 1)).hom) = ⊤ := by
      have h : ((Work.StemsB.relChainsR ℚ X A).d 0 (0 - 1)).hom = 0 := by
        simpa only [ModuleCat.hom_zero] using congrArg ModuleCat.Hom.hom
          (HomologicalComplex.shape (Work.StemsB.relChainsR ℚ X A) 0 0
            (by simp [ComplexShape.down]))
      rw [h, LinearMap.ker_zero]
    have hf0 : ((Work.StemsB.rdREquiv ℚ X A 0).symm
        (((Work.Cohomology.relComplex ℚ X A).iCycles 0).hom z)) = 0 := by
      ext x
      exact hvan x (by rw [hker]; exact Submodule.mem_top)
    have hφ0 : ((Work.Cohomology.relComplex ℚ X A).iCycles 0).hom z = 0 := by
      rw [← LinearEquiv.apply_symm_apply (Work.StemsB.rdREquiv ℚ X A 0)
        (((Work.Cohomology.relComplex ℚ X A).iCycles 0).hom z), hf0, map_zero]
    have hz0 : z = 0 := by
      apply Work.Cohomology.iCycles_injective_K (Work.Cohomology.relComplex ℚ X A) 0
      rw [hφ0, map_zero]
    rw [hz0, map_zero]
  · -- degree `m + 1`: the cochain is the coboundary of `rdREquiv g₀`
    have hγ : Work.Cohomology.relDiffLM ℚ X A m ((Work.StemsB.rdREquiv ℚ X A m) g₀)
        = ((Work.Cohomology.relComplex ℚ X A).iCycles (m + 1)).hom z := by
      have hg₀m : g₀.comp (((Work.StemsB.relChainsR ℚ X A).d (m + 1) m)).hom
          = (Work.StemsB.rdREquiv ℚ X A (m + 1)).symm
              (((Work.Cohomology.relComplex ℚ X A).iCycles (m + 1)).hom z) := by
        have h := hg₀'
        rwa [show ((Work.StemsB.relChainsR ℚ X A).d (m + 1) (m + 1 - 1))
              = ((Work.StemsB.relChainsR ℚ X A).d (m + 1) m) from rfl] at h
      have key : (Work.StemsB.rdREquiv ℚ X A (m + 1)).symm
            (Work.Cohomology.relDiffLM ℚ X A m ((Work.StemsB.rdREquiv ℚ X A m) g₀))
          = (Work.StemsB.rdREquiv ℚ X A (m + 1)).symm
              (((Work.Cohomology.relComplex ℚ X A).iCycles (m + 1)).hom z) := by
        rw [rdREquiv_symm_relDiffLM X A m g₀, hg₀m]
      exact (Work.StemsB.rdREquiv ℚ X A (m + 1)).symm.injective key
    have hzt : ((Work.Cohomology.relComplex ℚ X A).toCycles m (m + 1))
        ((Work.StemsB.rdREquiv ℚ X A m) g₀) = z := by
      apply Work.Cohomology.iCycles_injective_K (Work.Cohomology.relComplex ℚ X A) (m + 1)
      rw [show ((Work.Cohomology.relComplex ℚ X A).iCycles (m + 1)).hom
            (((Work.Cohomology.relComplex ℚ X A).toCycles m (m + 1))
              ((Work.StemsB.rdREquiv ℚ X A m) g₀))
          = ((Work.Cohomology.relComplex ℚ X A).d m (m + 1))
              ((Work.StemsB.rdREquiv ℚ X A m) g₀) from by
        have h := congrArg (fun (k : (Work.Cohomology.relComplex ℚ X A).X m ⟶
            (Work.Cohomology.relComplex ℚ X A).X (m + 1)) => ModuleCat.Hom.hom k
              ((Work.StemsB.rdREquiv ℚ X A m) g₀))
          (HomologicalComplex.toCycles_i (Work.Cohomology.relComplex ℚ X A) m (m + 1))
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h]
      rw [show ((Work.Cohomology.relComplex ℚ X A).d m (m + 1))
            ((Work.StemsB.rdREquiv ℚ X A m) g₀)
          = Work.Cohomology.relDiffLM ℚ X A m ((Work.StemsB.rdREquiv ℚ X A m) g₀) from by
        rw [Work.Cohomology.relComplex_d]; rfl]
      exact hγ
    rw [← hzt]
    have h := congrArg (fun (k : (Work.Cohomology.relComplex ℚ X A).X m ⟶
        (Work.Cohomology.relComplex ℚ X A).homology (m + 1)) => ModuleCat.Hom.hom k
          ((Work.StemsB.rdREquiv ℚ X A m) g₀))
      (HomologicalComplex.toCycles_comp_homologyπ (Work.Cohomology.relComplex ℚ X A) m (m + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h

/-! ## The relative Kronecker pairing over `ℚ` is a linear equivalence -/

theorem relKronEquiv (X : TopCat) (A : Set X) (n : ℕ) :
    ∃ e : ↥((Work.Cohomology.relComplex ℚ X A).homology n) ≃ₗ[ℚ]
        (↥((Work.StemsB.relChainsR ℚ X A).homology n) →ₗ[ℚ] ℚ),
      ∀ (φ : Work.Cohomology.relKern ℚ X A n)
        (hφ : Work.Cohomology.relDiffLM ℚ X A n φ = 0)
        (c : (Work.StemsB.relChainsR ℚ X A).cycles n)
        (x : (Work.Cohomology.singularChains ℚ X).X n)
        (hx : (Work.StemsB.rdRProj ℚ X A n) x = (Work.StemsB.relChainsR ℚ X A).iCycles n c),
        e (Work.Cohomology.relClassOf ℚ X A φ hφ)
          ((Work.StemsB.relChainsR ℚ X A).homologyπ n c)
            = Work.StemsB.rdRLM ℚ X n φ.1 x := by
  refine ⟨LinearEquiv.ofBijective ((relKronMapR ℚ X A n).hom)
    ⟨relKronMapRInjective X A n, relKronMapRSurjective X A n⟩, ?_⟩
  intro φ hφ c x hx
  simp only [LinearEquiv.ofBijective_apply]
  have hclass : Work.Cohomology.relClassOf ℚ X A φ hφ
      = ((Work.Cohomology.relComplex ℚ X A).homologyπ n)
        (Work.Cohomology.relCocycleOf ℚ X A φ hφ) := rfl
  rw [hclass, relKronMapR_apply, relKronLinR_apply, relKronFunLinR_apply]
  rw [show relOfCycleR ℚ X A n (Work.Cohomology.relCocycleOf ℚ X A φ hφ) = φ from
    Work.Cohomology.iCycles_relCocycleOf ℚ X A φ hφ]
  rw [← hx, relKronLMR_rdRProj]

end

end Work.Serre
