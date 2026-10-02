import Mathlib
import Submission.Work.Serre.relKron_exists
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Serre.csrDefs
import Submission.Work.Tubular.relKronH_natural
import Submission.Work.Serre.csrRelIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the rational relative Kronecker pairing

`Work.Serre.relKronMapR ℚ X A n : H^n(X,A;ℚ) →ₗ[ℚ] (H_n(X,A;ℚ) →ₗ[ℚ] ℚ)` is the relative
Kronecker pairing over `ℚ`, constructed in `Submission/Work/Serre/relKron_exists.lean` together
with its computation rule on the class of a relative cocycle (`relKronMapR_apply`).

This file proves its **naturality** in the pair: for a continuous map `f : X → Y` with
`f '' A ⊆ B`, a relative cohomology class `β ∈ H^n(Y,B;ℚ)` and a relative homology class
`c ∈ H_n(X,A;ℚ)` one has

  `⟨f^* β, c⟩_{(X,A)} = ⟨β, f_* c⟩_{(Y,B)}`.

The proof is a verbatim port of the integral statement (`Work.Tubular.relKronH_natural` /
`Work.ThomBordism.FrameSigns.relKronH_natural`) to the `ℚ`-coefficient model
`Work.StemsB.relChainsR ℚ`; the chain-level naturality of the quotient map `C_*(X) → C_*(X,A)` is
`Work.Serre.cokernel_π_relChainsRPairMap` (`Submission/Work/Serre/csrRelIso.lean`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace Work.Serre.B1Rel

open CategoryTheory

noncomputable section

/-- **The class of the relative cocycle attached to a relative cycle.** -/
private lemma relClassOf_relOfCycleR {R : Type} [CommRing R] (X : TopCat) (A : Set X) (n : ℕ)
    (z : (Work.Cohomology.relComplex R X A).cycles n) :
    Work.Cohomology.relClassOf R X A (Work.Serre.relOfCycleR R X A n z)
        (Work.Serre.relDiffLM_relOfCycleR R X A n z)
      = (HomologicalComplex.homologyπ (Work.Cohomology.relComplex R X A) n).hom z := by
  have h : Work.Cohomology.relCocycleOf R X A (Work.Serre.relOfCycleR R X A n z)
      (Work.Serre.relDiffLM_relOfCycleR R X A n z) = z := by
    apply Work.Cohomology.iCycles_injective_K (Work.Cohomology.relComplex R X A) n
    rw [Work.Cohomology.iCycles_relCocycleOf]
    rfl
  rw [Work.Cohomology.relClassOf, h]

/-- A morphism of complexes sends the class of a cycle to the class of the image cycle. -/
private lemma homologyMap_homologyπ_apply {R : Type} [CommRing R] {ι : Type}
    {cs : ComplexShape ι} {K L : HomologicalComplex (ModuleCat R) cs} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i).hom ((K.homologyπ i).hom z) =
      (L.homologyπ i).hom ((HomologicalComplex.cyclesMap φ i).hom z) := by
  have h := HomologicalComplex.homologyπ_naturality φ i
  have h2 := congrArg (fun g => g.hom z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The value of `rdRLM` is the evaluation of the underlying cochain. -/
private lemma rdRLM_apply {R : Type} [CommRing R] (Y : TopCat) (n : ℕ)
    (φ : ↥((Work.Cohomology.singularCochainComplex R Y).X n))
    (y : ↥((Work.Cohomology.singularChains R Y).X n)) :
    Work.StemsB.rdRLM R Y n φ y
      = (show ↥((Work.Cohomology.singularChains R Y).X n) →ₗ[R] R from φ) y := rfl

/-- **The computation rule for `relKronMapR` on the class of a relative cocycle.** -/
private lemma relKronMapR_apply_relClassOf {R : Type} [CommRing R] (X : TopCat) (A : Set X)
    (n : ℕ) (φ : Work.Cohomology.relKern R X A n)
    (hφ : Work.Cohomology.relDiffLM R X A n φ = 0)
    (c : (Work.StemsB.relChainsR R X A).cycles n) :
    (Work.Serre.relKronMapR R X A n).hom (Work.Cohomology.relClassOf R X A φ hφ)
        ((HomologicalComplex.homologyπ (Work.StemsB.relChainsR R X A) n).hom c)
      = (Work.Serre.relKronLMR R X A n φ)
          ((HomologicalComplex.iCycles (Work.StemsB.relChainsR R X A) n).hom c) := by
  have hclass : Work.Cohomology.relClassOf R X A φ hφ
      = (HomologicalComplex.homologyπ (Work.Cohomology.relComplex R X A) n).hom
          (Work.Cohomology.relCocycleOf R X A φ hφ) := rfl
  rw [hclass, Work.Serre.relKronMapR_apply, Work.Serre.relKronLinR_apply,
    Work.Serre.relKronFunLinR_apply]
  rw [show Work.Serre.relOfCycleR R X A n (Work.Cohomology.relCocycleOf R X A φ hφ)
      = ((Work.Cohomology.relComplex R X A).iCycles n).hom
          (Work.Cohomology.relCocycleOf R X A φ hφ) from rfl,
    Work.Cohomology.iCycles_relCocycleOf R X A φ hφ]

/-- **The chain-level naturality of the quotient map `C_*(X) → C_*(X,A)`**: the projection
`rdRProj` commutes with the map of relative chain complexes induced by a map of pairs. -/
private lemma rdRProj_relChainsRPairMap_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B) (n : ℕ) :
    (Work.StemsB.rdRProj ℚ (TopCat.of X) A n) ≫ (Work.Serre.relChainsRPairMap A B g hg).f n
      = (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)).f n
        ≫ (Work.StemsB.rdRProj ℚ (TopCat.of Y) B n) := by
  have h := congrArg (fun k => k.f n)
    (Work.Serre.cokernel_π_relChainsRPairMap A B g hg)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h
  simpa only [Work.StemsB.rdRProj] using h

theorem relKronMapR_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (β : (Work.Cohomology.relComplex ℚ (TopCat.of Y) B).homology n)
    (c : (Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology n) :
    (Work.Serre.relKronMapR ℚ (TopCat.of X) A n).hom
        ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℚ A B
          (TopCat.ofHom f) hf) n).hom β) c
      = (Work.Serre.relKronMapR ℚ (TopCat.of Y) B n).hom β
          ((HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap A B f hf) n).hom c) := by
  -- reduce to the classes of a relative cocycle of `(Y,B)` and a relative cycle of `(X,A)`
  obtain ⟨ζ, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.relComplex ℚ (TopCat.of Y) B).homologyπ n)).mp inferInstance β
  obtain ⟨cc, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homologyπ n)).mp inferInstance c
  -- the relative cocycle underlying `ζ`
  rw [← relClassOf_relOfCycleR (TopCat.of Y) B n ζ]
  set φY : Work.Cohomology.relKern ℚ (TopCat.of Y) B n :=
    Work.Serre.relOfCycleR ℚ (TopCat.of Y) B n ζ with hφYdef
  -- a lift of the relative cycle `cc`
  obtain ⟨x0, hx0⟩ := Work.StemsB.rdRProj_surjective ℚ (TopCat.of X) A n
    ((HomologicalComplex.iCycles (Work.StemsB.relChainsR ℚ (TopCat.of X) A) n).hom cc)
  -- the two chain-level computation rules
  have hcyc : ((HomologicalComplex.iCycles (Work.StemsB.relChainsR ℚ (TopCat.of Y) B) n)
        ((HomologicalComplex.cyclesMap (Work.Serre.relChainsRPairMap A B f hf) n) cc))
      = (Work.Serre.relChainsRPairMap A B f hf).f n
          ((HomologicalComplex.iCycles (Work.StemsB.relChainsR ℚ (TopCat.of X) A) n) cc) := by
    have h2 := congrArg (fun (k : (Work.StemsB.relChainsR ℚ (TopCat.of X) A).cycles n ⟶
        (Work.StemsB.relChainsR ℚ (TopCat.of Y) B).X n) => (ConcreteCategory.hom k) cc)
      (HomologicalComplex.cyclesMap_i (Work.Serre.relChainsRPairMap A B f hf) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  have hnat :
      (Work.Serre.relChainsRPairMap A B f hf).f n
          ((Work.StemsB.rdRProj ℚ (TopCat.of X) A n) x0)
        = (Work.StemsB.rdRProj ℚ (TopCat.of Y) B n)
            (((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).f n) x0) := by
    have h2 := congrArg (fun (k : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X n ⟶
        (Work.StemsB.relChainsR ℚ (TopCat.of Y) B).X n) => (ConcreteCategory.hom k) x0)
      (rdRProj_relChainsRPairMap_apply A B f hf n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  -- the left hand side
  have hL : (Work.Serre.relKronMapR ℚ (TopCat.of X) A n).hom
        ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℚ A B
          (TopCat.ofHom f) hf) n).hom (Work.Cohomology.relClassOf ℚ (TopCat.of Y) B φY
            (Work.Serre.relDiffLM_relOfCycleR ℚ (TopCat.of Y) B n ζ)))
        ((HomologicalComplex.homologyπ (Work.StemsB.relChainsR ℚ (TopCat.of X) A) n).hom cc)
      = Work.StemsB.rdRLM ℚ (TopCat.of X) n
          ↑(Work.Cohomology.relMapLM (X₁ := TopCat.of X) (X₂ := TopCat.of Y) ℚ A B
            (TopCat.ofHom f) hf n φY) x0 := by
    rw [Work.Cohomology.homologyMap_relComplexMap_relClassOf (X₁ := TopCat.of X)
      (X₂ := TopCat.of Y) ℚ A B (TopCat.ofHom f) hf φY
      (Work.Serre.relDiffLM_relOfCycleR ℚ (TopCat.of Y) B n ζ)]
    rw [relKronMapR_apply_relClassOf (R := ℚ) (X := TopCat.of X) (A := A) n
      (Work.Cohomology.relMapLM (X₁ := TopCat.of X) (X₂ := TopCat.of Y) ℚ A B
        (TopCat.ofHom f) hf n φY)
      (Work.Cohomology.relDiffLM_relMapLM (X₁ := TopCat.of X) (X₂ := TopCat.of Y) ℚ A B
        (TopCat.ofHom f) hf φY (Work.Serre.relDiffLM_relOfCycleR ℚ (TopCat.of Y) B n ζ)) cc]
    rw [← hx0, Work.Serre.relKronLMR_rdRProj]
  -- the right hand side
  have hR : (Work.Serre.relKronMapR ℚ (TopCat.of Y) B n).hom
        (Work.Cohomology.relClassOf ℚ (TopCat.of Y) B φY
          (Work.Serre.relDiffLM_relOfCycleR ℚ (TopCat.of Y) B n ζ))
        ((HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap A B f hf) n).hom
          ((HomologicalComplex.homologyπ (Work.StemsB.relChainsR ℚ (TopCat.of X) A) n).hom cc))
      = Work.StemsB.rdRLM ℚ (TopCat.of Y) n ↑φY
          (((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).f n) x0) := by
    rw [homologyMap_homologyπ_apply (Work.Serre.relChainsRPairMap A B f hf) n cc]
    rw [relKronMapR_apply_relClassOf (R := ℚ) (X := TopCat.of Y) (A := B) n φY
      (Work.Serre.relDiffLM_relOfCycleR ℚ (TopCat.of Y) B n ζ)
      ((HomologicalComplex.cyclesMap (Work.Serre.relChainsRPairMap A B f hf) n) cc)]
    rw [hcyc, ← hx0, hnat, Work.Serre.relKronLMR_rdRProj]
  -- the two evaluations agree
  have hfin : Work.StemsB.rdRLM ℚ (TopCat.of X) n
        ↑(Work.Cohomology.relMapLM (X₁ := TopCat.of X) (X₂ := TopCat.of Y) ℚ A B
          (TopCat.ofHom f) hf n φY) x0
      = Work.StemsB.rdRLM ℚ (TopCat.of Y) n ↑φY
          (((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).f n) x0) := by
    let αL : Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj (TopCat.of X)) n :=
      (Work.Cohomology.relMapLM (X₁ := TopCat.of X) (X₂ := TopCat.of Y) ℚ A B
        (TopCat.ofHom f) hf n φY).1
    let αR : Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj (TopCat.of Y)) n := φY.1
    have h12 : αL = ((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y)
        (TopCat.ofHom f)).f n).hom.dualMap αR :=
      (Work.Cohomology.relMapLM_coe (X₁ := TopCat.of X) (X₂ := TopCat.of Y) ℚ A B
        (TopCat.ofHom f) hf n φY).trans
        (congrArg (fun ψ => ψ αR)
          (Work.Cohomology.dualChainMap_f_hom ℚ (TopCat.of X) (TopCat.of Y)
            (TopCat.ofHom f) n))
    rw [rdRLM_apply, rdRLM_apply]
    change αL x0 = αR (((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom f)).f n) x0)
    rw [h12]
    exact LinearMap.dualMap_apply _ _ _
  exact hL.trans (hfin.trans hR.symm)

end

end Work.Serre.B1Rel
