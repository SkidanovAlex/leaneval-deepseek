import Mathlib
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.relCapH
import Submission.Work.Cohomology.relCapH_kronH_cup
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.uctDual
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.cupUnit
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.trivialDiscBundlePair
import Submission.Work.Cohomology.trivialDiscBundlePairHomology
import Submission.Work.Cohomology.diskPairCohomologyTop
import Submission.Work.Cohomology.diskPairHomologyTop

/-!
# The relative cap product of the trivial rank-`4` disc bundle pair is nonzero (compat copy)

A `namespace Work.Cohomology.Compat` transplant of
`Submission/Work/Cohomology/diskPair_relCapPair_ne_zero.lean` that avoids importing
`Submission.Work.Cohomology.relComplexIsoDualZ` (hence `Submission.Work.Cohomology.dualZ`), whose
name `Work.Cohomology.dualZ` clashes with the identically named declaration of
`Submission.Work.Cohomology.localCohomology`.  Nothing here uses `relComplexIsoDualZ`; the pinned
comparison `C^*(X,A;ℤ) ≅ Hom_ℤ(C_*(X,A),ℤ)` used below is built directly from `relCochainDual`.

* `relDualComplexIso` — the pinned degreewise comparison `C^*(X,A;ℤ) ≅ Hom_ℤ(C_*(X,A),ℤ)`.
* `relDualLM_cap_zero` — chain level `⟨1, c ⌢ α⟩ = ⟨α, c⟩`.
* `relCapPair_kronH_eq_gen` / `relCapPair_kronH_eq` — the relative cap product against the unit
  class computes the universal-coefficient evaluation.
* `diskPairRelCapPair_ne_zero` — the target: for the pair `(D⁴×D⁴, D⁴×S³)` there are nonzero `u`,
  `z` with `u ⌢ z ≠ 0`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology.Compat

noncomputable section

/-- The total space `D⁴ × D⁴` of the trivial rank-`4` disc bundle over `D⁴`. -/
abbrev tdpX : TopCat := TopCat.of (↥(diskUnit 4) × ↥(diskUnit 4))

/-- The unit sphere bundle `D⁴ × S³` inside `D⁴ × D⁴`. -/
abbrev tdpA : Set tdpX := {p | p.2 ∈ sphereInUnit 4}

/-! ## The pinned comparison `C^*(X,A;ℤ) ≅ Hom_ℤ(C_*(X,A), ℤ)`

`Work.Cohomology.relCochainDual` proves that the relative cochain complex is isomorphic to the
`ℤ`-dual of the relative chain complex, with degreewise components `relDualIso`.  We pin the
isomorphism once and for all (`relDualComplexIso`) so that its components are known. -/

/-- The pinned isomorphism `C^*(X,A;ℤ) ≅ Hom_ℤ(C_*(X,A), ℤ)`. -/
noncomputable def relDualComplexIso (X : TopCat) (A : Set X) :
    relComplex ℤ X A ≅ dualComplex ℤ (relChains X A) :=
  (HomologicalComplex.Hom.isoOfComponents (fun n => relDualIso X A n)
    (fun i j hij => by rw [← hij]; exact relDualIso_comm X A i)).symm

/-- The `n`-th component of `relDualComplexIso` is the inverse of `relDualIso`. -/
lemma relDualComplexIso_hom_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relDualComplexIso X A).hom.f n = (relDualIso X A n).inv :=
  HomologicalComplex.Hom.isoOfComponents_inv_f (fun n => relDualIso X A n)
    (fun i j hij => by rw [← hij]; exact relDualIso_comm X A i) n

/-- The inverse of `relDualIso` is the inverse of the linear equivalence `relDualEquiv`. -/
lemma relDualIso_inv_apply (X : TopCat) (A : Set X) (n : ℕ) (φ : relKern ℤ X A n) :
    (relDualIso X A n).inv.hom φ
      = ((relDualEquiv X A n).symm φ : (relChains X A).X n →ₗ[ℤ] ℤ) := rfl

/-! ## The chain level unit identity -/

/-- **The unit `0`-cochain of `cap α 0 c` is the evaluation of `α` at `c`.**  This is the
chain-level form of `⟨1, c ⌢ α⟩ = ⟨α, c⟩`. -/
lemma relDualLM_cap_zero (X : TopCat) (n : ℕ) (α : Cochain ℤ (TopCat.toSSet.obj X) n)
    (c : (singularChains ℤ X).X n) :
    unitCochain ℤ (TopCat.toSSet.obj X) (cap ℤ (TopCat.toSSet.obj X) α 0 c)
      = relDualLM X n α c := by
  change kronecker ℤ (TopCat.toSSet.obj X) (unitCochain ℤ (TopCat.toSSet.obj X))
      (cap ℤ (TopCat.toSSet.obj X) α 0 c) = kronecker ℤ (TopCat.toSSet.obj X) α c
  rw [kronecker_cap_cup ℤ (TopCat.toSSet.obj X) α (unitCochain ℤ (TopCat.toSSet.obj X)) c,
    (cupUnit ℤ (TopCat.toSSet.obj X) α).2]

/-! ## The comparison of the relative cap product with the universal coefficient evaluation -/

/-- **The comparison on generators.**  For a relative cocycle `zα` and a relative cycle `c`, the
Kronecker pairing of the unit class with the relative cap product `(zα ⌢ c)` equals the value of
the dual universal coefficient evaluation of `zα` at `c`.

Both sides are computed at the chain level: the left hand side evaluates the underlying cochain of
`zα` at a lift of `c` to an absolute chain (`relDualLM_cap_zero`), and the right hand side is
`dval E n (iCycles (cyclesMap zα)) (iCycles c)`, which is the same evaluation by
`relDualEquiv_symm_comp`. -/
lemma relCapPair_kronH_eq_gen (X : TopCat) (A : Set X) (n : ℕ)
    (e : (dualComplex ℤ (relChains X A)).homology n ≅
      ModuleCat.of ℤ (↥((relChains X A).homology n) →ₗ[ℤ] ℤ))
    (he : ∀ (z : ↥((dualComplex ℤ (relChains X A)).cycles n))
      (c : ↥((relChains X A).cycles (n + 0))),
      e.hom (((dualComplex ℤ (relChains X A)).homologyπ n) z)
          (((relChains X A).homologyπ (n + 0)) c)
        = dval (relChains X A) n (((dualComplex ℤ (relChains X A)).iCycles n) z)
            (((relChains X A).iCycles (n + 0)) c))
    (zα : (relComplex ℤ X A).cycles n) (c : (relChains X A).cycles (n + 0)) :
    kronH ℤ (TopCat.toSSet.obj X) 0 (oneH ℤ (TopCat.toSSet.obj X))
        (relCapPair X A n 0 (((relComplex ℤ X A).homologyπ n) zα)
          (((relChains X A).homologyπ (n + 0)) c))
      = e.hom ((HomologicalComplex.homologyMap (relDualComplexIso X A).hom n)
            (((relComplex ℤ X A).homologyπ n) zα))
          (((relChains X A).homologyπ (n + 0)) c) := by
  obtain ⟨c'', hc''⟩ : ∃ x : (singularChains ℤ X).X (n + 0),
      (ModuleCat.Hom.hom (relDualProj X A (n + 0))) x
        = (ModuleCat.Hom.hom ((relChains X A).iCycles (n + 0))) c :=
    relDualProj_surjective X A (n + 0) (((relChains X A).iCycles (n + 0)) c)
  -- the lift of the relative cycle, as a cokernel class
  have hstep : (relChains_cokernelIso X A (n + 0)).hom ((relChains X A).iCycles (n + 0) c)
      = (ModuleCat.Hom.hom (cokernel.π ((inclChains X A).f (n + 0)))) c'' := by
    rw [← hc'']
    exact relChains_cokernelIso_canon_apply X A (n + 0) c''
  -- the left hand side
  have hLHS : kronH ℤ (TopCat.toSSet.obj X) 0 (oneH ℤ (TopCat.toSSet.obj X))
      (relCapPair X A n 0 (((relComplex ℤ X A).homologyπ n) zα)
        (((relChains X A).homologyπ (n + 0)) c))
      = relDualLM X n ((((relComplex ℤ X A).iCycles n) zα).1) c'' := by
    calc kronH ℤ (TopCat.toSSet.obj X) 0 (oneH ℤ (TopCat.toSSet.obj X))
          (relCapPair X A n 0 (((relComplex ℤ X A).homologyπ n) zα)
            (((relChains X A).homologyπ (n + 0)) c))
        = kronH ℤ (TopCat.toSSet.obj X) 0 (oneH ℤ (TopCat.toSSet.obj X))
            (((singularChains ℤ X).homologyπ 0) (relCapPairZ X A n 0 zα c)) :=
          congrArg (fun x => kronH ℤ (TopCat.toSSet.obj X) 0 (oneH ℤ (TopCat.toSSet.obj X)) x)
            (relCapPair_apply X A n 0 zα c)
      _ = (unitCochain ℤ (TopCat.toSSet.obj X))
            (((singularChains ℤ X).iCycles 0) (relCapPairZ X A n 0 zα c)) := by
          rw [show oneH ℤ (TopCat.toSSet.obj X)
              = cohomologyClassOf ℤ (TopCat.toSSet.obj X) (unitCochain ℤ (TopCat.toSSet.obj X))
                  (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj X)) from rfl]
          exact kronH_apply_sing X (unitCochain ℤ (TopCat.toSSet.obj X))
            (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj X)) (relCapPairZ X A n 0 zα c)
      _ = (unitCochain ℤ (TopCat.toSSet.obj X))
            (relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n) zα) 0
              ((relChains_cokernelIso X A (n + 0)).hom ((relChains X A).iCycles (n + 0) c))) :=
          congrArg (unitCochain ℤ (TopCat.toSSet.obj X)) (relCapPairZ_iCycles X A n 0 zα c)
      _ = (unitCochain ℤ (TopCat.toSSet.obj X))
            (relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n) zα) 0
              ((ModuleCat.Hom.hom (cokernel.π ((inclChains X A).f (n + 0)))) c'')) :=
          congrArg (fun x => (unitCochain ℤ (TopCat.toSSet.obj X))
            (relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n) zα) 0 x)) hstep
      _ = (unitCochain ℤ (TopCat.toSSet.obj X))
            (cap ℤ (TopCat.toSSet.obj X) ((((relComplex ℤ X A).iCycles n) zα).1) 0 c'') :=
          congrArg (unitCochain ℤ (TopCat.toSSet.obj X))
            (relCapHalf_apply_incl X A (((relComplex ℤ X A).iCycles n) zα) c'')
      _ = relDualLM X n ((((relComplex ℤ X A).iCycles n) zα).1) c'' :=
          relDualLM_cap_zero X n ((((relComplex ℤ X A).iCycles n) zα).1) c''
  -- the right hand side
  have hcyc : ((dualComplex ℤ (relChains X A)).iCycles n)
        ((HomologicalComplex.cyclesMap (relDualComplexIso X A).hom n) zα)
      = ((relDualEquiv X A n).symm (((relComplex ℤ X A).iCycles n) zα)) := by
    have h := congrArg (fun (k : (relComplex ℤ X A).cycles n ⟶
        (dualComplex ℤ (relChains X A)).X n) => (ModuleCat.Hom.hom k) zα)
      (HomologicalComplex.cyclesMap_i (relDualComplexIso X A).hom n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, relDualComplexIso_hom_f]
    exact relDualIso_inv_apply X A n (((relComplex ℤ X A).iCycles n) zα)
  have hnat2 : (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (relDualComplexIso X A).hom n))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ X A) n)) zα)
      = (ModuleCat.Hom.hom
          (HomologicalComplex.homologyπ (dualComplex ℤ (relChains X A)) n))
        ((HomologicalComplex.cyclesMap (relDualComplexIso X A).hom n) zα) := by
    have h := congrArg (fun (k : (relComplex ℤ X A).cycles n ⟶
        (dualComplex ℤ (relChains X A)).homology n) => (ModuleCat.Hom.hom k) zα)
      (HomologicalComplex.homologyπ_naturality (relDualComplexIso X A).hom n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have hRHS : e.hom ((HomologicalComplex.homologyMap (relDualComplexIso X A).hom n)
        (((relComplex ℤ X A).homologyπ n) zα))
        (((relChains X A).homologyπ (n + 0)) c)
      = relDualLM X n ((((relComplex ℤ X A).iCycles n) zα).1) c'' := by
    calc e.hom ((HomologicalComplex.homologyMap (relDualComplexIso X A).hom n)
          (((relComplex ℤ X A).homologyπ n) zα)) (((relChains X A).homologyπ (n + 0)) c)
        = e.hom (((dualComplex ℤ (relChains X A)).homologyπ n)
              ((HomologicalComplex.cyclesMap (relDualComplexIso X A).hom n) zα))
            (((relChains X A).homologyπ (n + 0)) c) := by
          rw [hnat2]
      _ = dval (relChains X A) n
            (((dualComplex ℤ (relChains X A)).iCycles n)
              ((HomologicalComplex.cyclesMap (relDualComplexIso X A).hom n) zα))
            (((relChains X A).iCycles (n + 0)) c) :=
          he ((HomologicalComplex.cyclesMap (relDualComplexIso X A).hom n) zα) c
      _ = dval (relChains X A) n
            ((relDualEquiv X A n).symm (((relComplex ℤ X A).iCycles n) zα))
            (((relChains X A).iCycles (n + 0)) c) := by
          rw [hcyc]
      _ = dval (relChains X A) n
            ((relDualEquiv X A n).symm (((relComplex ℤ X A).iCycles n) zα))
            ((ModuleCat.Hom.hom (relDualProj X A (n + 0))) c'') := by
          rw [← hc'']
      _ = relDualLM X n ((((relComplex ℤ X A).iCycles n) zα).1) c'' := by
          have hE := LinearMap.congr_fun
            (relDualEquiv_symm_comp X A n (((relComplex ℤ X A).iCycles n) zα)) c''
          rw [LinearMap.comp_apply] at hE
          exact hE
  rw [hLHS, hRHS]

/-! ## The comparison of the relative cap product with the universal coefficient evaluation -/

lemma relCapPair_kronH_eq (X : TopCat) (A : Set X) (n : ℕ)
    (e : (dualComplex ℤ (relChains X A)).homology n ≅
      ModuleCat.of ℤ (↥((relChains X A).homology n) →ₗ[ℤ] ℤ))
    (he : ∀ (z : ↥((dualComplex ℤ (relChains X A)).cycles n))
      (c : ↥((relChains X A).cycles (n + 0))),
      e.hom (((dualComplex ℤ (relChains X A)).homologyπ n) z)
          (((relChains X A).homologyπ (n + 0)) c)
        = dval (relChains X A) n (((dualComplex ℤ (relChains X A)).iCycles n) z)
            (((relChains X A).iCycles (n + 0)) c))
    (u : relCohomology ℤ X A n) (z : (relChains X A).homology n) :
    kronH ℤ (TopCat.toSSet.obj X) 0 (oneH ℤ (TopCat.toSSet.obj X))
        (relCapPair X A n 0 u z)
      = e.hom ((HomologicalComplex.homologyMap (relDualComplexIso X A).hom n) u) z := by
  obtain ⟨zα, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relComplex ℤ X A).homologyπ n)).mp inferInstance u
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relChains X A).homologyπ (n + 0))).mp inferInstance z
  exact relCapPair_kronH_eq_gen X A n e he zα c

/-! ## The main theorem -/

theorem diskPairRelCapPair_ne_zero :
    ∃ (u : Work.Cohomology.relCohomology ℤ
          (TopCat.of (↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4)))
          {p : ↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4) |
            p.2 ∈ Work.Cohomology.sphereInUnit 4} 4)
      (z : (Work.Cohomology.relChains
          (TopCat.of (↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4)))
          {p : ↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4) |
            p.2 ∈ Work.Cohomology.sphereInUnit 4}).homology 4),
      u ≠ 0 ∧ z ≠ 0 ∧
        (Work.Cohomology.relCapPair
          (TopCat.of (↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4)))
          {p : ↥(Work.Cohomology.diskUnit 4) × ↥(Work.Cohomology.diskUnit 4) |
            p.2 ∈ Work.Cohomology.sphereInUnit 4} 4 0 u z) ≠ 0 := by
  change ∃ (u : relCohomology ℤ tdpX tdpA 4) (z : (relChains tdpX tdpA).homology 4),
      u ≠ 0 ∧ z ≠ 0 ∧ relCapPair tdpX tdpA 4 0 u z ≠ 0
  -- the relative homology of the pair is free
  have hfree : ∀ k, Module.Free ℤ ↥((relChains tdpX tdpA).homology k) := by
    intro k
    obtain ⟨ek⟩ := trivialDiscBundlePairHomology k
    haveI : Module.Free ℤ ↥(ModuleCat.of ℤ (Fin (if k = 4 then 1 else 0) → ℤ)) := inferInstance
    exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
      (uctIsoToLinearEquiv ek).symm
  obtain ⟨e, he⟩ := uctDual_evaluation (relChains tdpX tdpA)
    (relChainsProjective tdpX tdpA) hfree 4
  -- the homology map of the pinned identification is an isomorphism
  haveI hmm : IsIso (HomologicalComplex.homologyMap (relDualComplexIso tdpX tdpA).hom 4) :=
    IsIso.mk ⟨HomologicalComplex.homologyMap (relDualComplexIso tdpX tdpA).inv 4, by
        rw [← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id,
          HomologicalComplex.homologyMap_id], by
        rw [← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
          HomologicalComplex.homologyMap_id]⟩
  -- a nonzero relative cohomology class
  obtain ⟨isoC⟩ := trivialDiscBundlePair 4
  have hne1 : (fun _ => (1 : ℤ) : Fin (if (4 : ℕ) = 4 then 1 else 0) → ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h (0 : Fin 1))
  let u₀ : relCohomology ℤ tdpX tdpA 4 := isoC.inv.hom (fun _ => (1 : ℤ))
  have hhom : isoC.hom.hom u₀ = (fun _ => (1 : ℤ)) :=
    Iso.inv_hom_id_apply isoC (fun _ => (1 : ℤ))
  have hu₀ : u₀ ≠ 0 := by
    intro h
    have h2 : isoC.hom.hom u₀ = 0 := by rw [h, map_zero]
    rw [hhom] at h2
    exact hne1 h2
  -- the image of `u₀` under the universal coefficient evaluation is nonzero
  have hUu₀ : e.hom ((HomologicalComplex.homologyMap (relDualComplexIso tdpX tdpA).hom 4) u₀)
      ≠ 0 := by
    intro h0
    have h1 : (HomologicalComplex.homologyMap (relDualComplexIso tdpX tdpA).hom 4) u₀ = 0 :=
      (ModuleCat.mono_iff_injective e.hom).mp inferInstance (by rw [h0, map_zero])
    exact hu₀ ((ModuleCat.mono_iff_injective
      (HomologicalComplex.homologyMap (relDualComplexIso tdpX tdpA).hom 4)).mp inferInstance
        (by rw [h1, map_zero]))
  obtain ⟨z, hz⟩ : ∃ z : (relChains tdpX tdpA).homology 4,
      e.hom ((HomologicalComplex.homologyMap (relDualComplexIso tdpX tdpA).hom 4) u₀) z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hUu₀ (LinearMap.ext h)
  refine ⟨u₀, z, hu₀, ?_, ?_⟩
  · intro hz0
    exact hz (by rw [hz0, map_zero])
  · intro hcap
    have hk := relCapPair_kronH_eq tdpX tdpA 4 e he u₀ z
    rw [hcap, map_zero] at hk
    exact hz hk.symm

end

end Work.Cohomology.Compat
