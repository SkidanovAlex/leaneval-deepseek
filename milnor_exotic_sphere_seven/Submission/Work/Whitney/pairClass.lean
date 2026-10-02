import Mathlib
import Submission.Work.Whitney.CupDefs
import Submission.Work.Whitney.tcmSuspAux.pairing
import Submission.Work.Whitney.RelABComplex
import Submission.Work.Whitney.RankTwo.RepDefs
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Whitney.relABZ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology

namespace Work.Whitney

noncomputable section

/-!
# The evaluation of an `A+C`-cycle on the class `tcmRelCup (pr₁^* Mpun n) (pr₂^* Mpun 1)`

The lemma `Work.Whitney.pairClass` is the step that turns a *class* identity
`tcmRelCup … = k • tcmF^* (Mpun (n+1))` into the corresponding identity of Kronecker pairings with
an `A+C`-cycle `Z`.  Its content is the well-definedness of the pairing `⟨γ, Z⟩` of an
`(A∪C)`-relative cocycle with a chain whose boundary is annihilated by every `A+C`-cochain
(the "pairing trick" of `Submission/Work/Whitney/tcmSuspAux/pairing.lean`), together with two
bookkeeping facts:

* the class `tcmF^* (Mpun (n+1))` is represented by the pullback of any representative `s` of
  `Mpun (n+1)` (naturality of `relCohMap` on classes, `homologyMap_relComplexMap_relClassOf`);
* the underlying cochain of that pullback is `(dualChainMap tcmF).f (n+1) s.1`
  (`relMapLM_coe`).

The pairing-independence lemma is isolated below as `kronecker_eq_of_relClassOf_eq_pdAB`; it is the
`A+C`-version of `Work.Cohomology.kronecker_relComplex_eq_of_homology_eq`, with the hypothesis
`IsSmallChain A ∅ (∂Z)` (the boundary of `Z` is carried by `A`) replaced by the hypothesis that
every element of the `A+C`-complex `C^k(X,A) ∩ C^k(X,C)` kills `∂Z`.  Both hypotheses make the
pairing of a *coboundary* `δ η ∈ C^{k+1}(X, A∪C)` with `Z` vanish: in the second, the relevant
`η` vanishes on `A ∪ C`, hence lies in `C^k(X,A) ∩ C^k(X,C)`.
-/

/-- **Bridge**: a relative cochain is a cocycle for `relDiffLM` iff it is a cocycle for the
differential of `relComplex` (a local copy of `Work.Cohomology.relDiffLM_eq_zero_iff`). -/
theorem relDiffLM_eq_zero_iff_local (X : TopCat) (A : Set X) (k : ℕ)
    (x : ↥(relKern ℤ X A k)) :
    ((ModuleCat.Hom.hom ((relComplex ℤ X A).d k (k + 1))) x = 0)
      ↔ relDiffLM ℤ X A k x = 0 := by
  constructor <;> intro h
  · rwa [relComplex_d, relDiff, ModuleCat.hom_ofHom] at h
  · rwa [relComplex_d, relDiff, ModuleCat.hom_ofHom]

/-- `homologyπ` is `ℤ`-linear on cycles (local copy of
`Work.Cohomology.homologyπ_smul_K_int`). -/
theorem homologyπ_smul_K_int_local (K : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (c : ℤ)
    (z : K.cycles n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) (c • z)
      = c • (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) z := by
  rw [← Int.cast_smul_eq_zsmul ℤ c z, LinearMap.map_smul, Int.cast_smul_eq_zsmul]

/-- **Scalar multiplication of relative classes** (local copy of
`Work.Cohomology.relClassOf_smul`). -/
theorem relClassOf_smul_local (X : TopCat) (A : Set X) (n : ℕ) (c : ℤ)
    (a : relKern ℤ X A n) (h : relDiffLM ℤ X A n (c • a) = 0)
    (h' : relDiffLM ℤ X A n a = 0) :
    relClassOf ℤ X A (c • a) h = c • relClassOf ℤ X A a h' := by
  rw [relClassOf, relClassOf]
  rw [← homologyπ_smul_K_int_local (relComplex ℤ X A) n c (relCocycleOf ℤ X A a h')]
  congr 1
  apply iCycles_injective_K (relComplex ℤ X A) n
  calc (ModuleCat.Hom.hom (HomologicalComplex.iCycles (relComplex ℤ X A) n))
        (relCocycleOf ℤ X A (c • a) h)
      = c • a := iCycles_relCocycleOf ℤ X A (c • a) h
    _ = c • (ModuleCat.Hom.hom (HomologicalComplex.iCycles (relComplex ℤ X A) n))
          (relCocycleOf ℤ X A a h') := by rw [iCycles_relCocycleOf]
    _ = (ModuleCat.Hom.hom (HomologicalComplex.iCycles (relComplex ℤ X A) n))
          (c • relCocycleOf ℤ X A a h') := by
          rw [← Int.cast_smul_eq_zsmul ℤ c (relCocycleOf ℤ X A a h')]
          rw [LinearMap.map_smul]
          rw [Int.cast_smul_eq_zsmul]

/-- **Stokes** for the Kronecker pairing, in the singular spelling. -/
theorem kronecker_cochainDiff_local {X : TopCat} {k : ℕ}
    (b : Cochain ℤ (TopCat.toSSet.obj X) k) (Z : (singularChains ℤ X).X (k + 1)) :
    kronecker ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) b) Z
      = kronecker ℤ (TopCat.toSSet.obj X) b
          (((singularChains ℤ X).d (k + 1) k) Z) := rfl

/-- **The pairing of an `(A∪C)`-relative cocycle with an `A+C`-cycle depends only on the class.**

Two relative `(k+1)`-cocycles of the pair `(X, A∪C)` with the same cohomology class pair equally
with every `(k+1)`-chain `Z` whose boundary is annihilated by every element of the `A+C`-complex
`C^k(X, A+C) = C^k(X,A) ∩ C^k(X,C)`. -/
theorem kronecker_eq_of_relClassOf_eq_pdAB {X : TopCat} (A C : Set X) (k : ℕ)
    (γ γ' : ↥(relKern ℤ X (A ∪ C) (k + 1)))
    (hγ : relDiffLM ℤ X (A ∪ C) (k + 1) γ = 0)
    (hγ' : relDiffLM ℤ X (A ∪ C) (k + 1) γ' = 0)
    (h : relClassOf ℤ X (A ∪ C) γ hγ = relClassOf ℤ X (A ∪ C) γ' hγ')
    (Z : (singularChains ℤ X).X (k + 1))
    (hZ : ∀ ξ : (pdABCohR (R := ℤ) X A C).X k,
        kronecker ℤ (TopCat.toSSet.obj X) ξ.1
          (((singularChains ℤ X).d (k + 1) k) Z) = 0) :
    kronecker ℤ (TopCat.toSSet.obj X)
        (show Cochain ℤ (TopCat.toSSet.obj X) (k + 1) from γ.1) Z
      = kronecker ℤ (TopCat.toSSet.obj X)
        (show Cochain ℤ (TopCat.toSSet.obj X) (k + 1) from γ'.1) Z := by
  classical
  have hγd : (ModuleCat.Hom.hom ((relComplex ℤ X (A ∪ C)).d (k + 1) (k + 1 + 1))) γ = 0 :=
    (relDiffLM_eq_zero_iff_local X (A ∪ C) (k + 1) γ).mpr hγ
  have hγd' : (ModuleCat.Hom.hom ((relComplex ℤ X (A ∪ C)).d (k + 1) (k + 1 + 1))) γ' = 0 :=
    (relDiffLM_eq_zero_iff_local X (A ∪ C) (k + 1) γ').mpr hγ'
  have hlin : (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ X (A ∪ C)) (k + 1)))
        (cocycleOfK (relComplex ℤ X (A ∪ C)) γ hγd)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ X (A ∪ C)) (k + 1)))
        (cocycleOfK (relComplex ℤ X (A ∪ C)) γ' hγd') := by
    rw [← relClassOf_eq_homologyπ_cocycleOfK ℤ X (A ∪ C) γ hγ hγd,
      ← relClassOf_eq_homologyπ_cocycleOfK ℤ X (A ∪ C) γ' hγ' hγd']
    exact h
  have hd : (relComplex ℤ X (A ∪ C)).d (k + 1) (k + 1 + 1) (γ - γ') = 0 := by
    rw [map_sub, hγd, hγd', sub_self]
  have hcyc : cocycleOfK (relComplex ℤ X (A ∪ C)) (γ - γ') hd
      = cocycleOfK (relComplex ℤ X (A ∪ C)) γ hγd
        - cocycleOfK (relComplex ℤ X (A ∪ C)) γ' hγd' := by
    apply (ModuleCat.mono_iff_injective ((relComplex ℤ X (A ∪ C)).iCycles (k + 1))).mp inferInstance
    rw [map_sub, iCycles_cocycleOfK, iCycles_cocycleOfK, iCycles_cocycleOfK]
  have hzero : (relComplex ℤ X (A ∪ C)).homologyπ (k + 1)
      (cocycleOfK (relComplex ℤ X (A ∪ C)) (γ - γ') hd) = 0 := by
    rw [hcyc, map_sub, hlin, sub_self]
  obtain ⟨η, hη⟩ :=
    pd_us_ab_resolve_exists_of_homologyπ_eq_zero (relComplex ℤ X (A ∪ C)) k _ hzero
  have hη' : γ - γ' = (relComplex ℤ X (A ∪ C)).d k (k + 1) η := by
    rw [hη, iCycles_cocycleOfK]
  have hcoe : (γ.1 - γ'.1 : Cochain ℤ (TopCat.toSSet.obj X) (k + 1))
      = cochainDiff ℤ (TopCat.toSSet.obj X) (show Cochain ℤ (TopCat.toSSet.obj X) k from η.1) := by
    have h2 : ((γ - γ').1 : Cochain ℤ (TopCat.toSSet.obj X) (k + 1))
        = (((relComplex ℤ X (A ∪ C)).d k (k + 1)) η).1 := congrArg Subtype.val hη'
    rw [show (γ.1 - γ'.1 : Cochain ℤ (TopCat.toSSet.obj X) (k + 1)) = (γ - γ').1 from rfl, h2,
      relComplex_d]
    simp only [relDiff, ModuleCat.hom_ofHom]
    exact singularCochain_d_apply ℤ X (show Cochain ℤ (TopCat.toSSet.obj X) k from η.1)
  have heval : kronecker ℤ (TopCat.toSSet.obj X)
      (cochainDiff ℤ (TopCat.toSSet.obj X)
        (show Cochain ℤ (TopCat.toSSet.obj X) k from η.1)) Z = 0 := by
    have hdZ := hZ (⟨η.1, Submodule.mem_inf.mpr
      ⟨relKern_mono (R := ℤ) (Set.subset_union_left : A ⊆ A ∪ C) η.2,
       relKern_mono (R := ℤ) (Set.subset_union_right : C ⊆ A ∪ C) η.2⟩⟩ :
        (pdABCohR (R := ℤ) X A C).X k)
    rw [kronecker_cochainDiff_local]
    exact hdZ
  have hsum : (show Cochain ℤ (TopCat.toSSet.obj X) (k + 1) from γ'.1)
      + cochainDiff ℤ (TopCat.toSSet.obj X)
          (show Cochain ℤ (TopCat.toSSet.obj X) k from η.1)
      = (show Cochain ℤ (TopCat.toSSet.obj X) (k + 1) from γ.1) := by
    rw [← hcoe]
    abel
  rw [← hsum]
  rw [kronecker_add, heval, add_zero]

/-- The pullback of a relative class of the punctured pair `(Y × ℝ^{n+1}, Punct Y (n+1))` to
the pair `(tcmX Y n 1, A ∪ C)`, along the coordinate identification `tcmF`. -/
abbrev pullRel (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (s : ↥(relKern ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) (n + 1))) :
    ↥(relKern ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1)) :=
  relMapLM (X₁ := TopCat.of (tcmX Y n 1))
    (X₂ := TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1)))) ℤ
    (tcmA Y n 1 ∪ tcmC Y n 1) (Work.Thom.Punct Y (n + 1))
    (TopCat.ofHom (tcmF Y n 1)) (tcmF_mem Y n 1) (n + 1) s

/-- The pullback of a cocycle is a cocycle. -/
theorem pullRel_coc (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (s : ↥(relKern ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) (n + 1)))
    (hs : relDiffLM ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) (n + 1) s = 0) :
    relDiffLM ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1)
      (pullRel Y n s) = 0 :=
  relDiffLM_relMapLM (R := ℤ) (X₁ := TopCat.of (tcmX Y n 1))
    (X₂ := TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
    (tcmA Y n 1 ∪ tcmC Y n 1) (Work.Thom.Punct Y (n + 1))
    (TopCat.ofHom (tcmF Y n 1)) (tcmF_mem Y n 1) s hs

/-- The underlying cochain of the pullback is the pullback of the underlying cochain. -/
theorem pullRel_coe (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (s : ↥(relKern ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) (n + 1))) :
    (pullRel Y n s).1 = (ModuleCat.Hom.hom ((dualChainMap ℤ (TopCat.of (tcmX Y n 1))
      (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (TopCat.ofHom (tcmF Y n 1))).f (n + 1))) s.1 := rfl

theorem pairClass (Y : Type) [TopologicalSpace Y] (n : ℕ) (k : ℤ)
    (h : Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y n 1) (Work.Whitney.tcmC Y n 1)
        (Work.Whitney.isOpen_tcmA Y n 1) (Work.Whitney.isOpen_tcmC Y n 1) n 1
        ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y n 1) (Work.Whitney.tcmA Y n 1)
          (Work.Thom.Punct Y n) (fun x hx => hx) ℤ n).hom (Work.Thom.Mpun n Y))
        ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y n 1) (Work.Whitney.tcmC Y n 1)
          (Work.Thom.Punct Y 1) (fun x hx => hx) ℤ 1).hom (Work.Thom.Mpun 1 Y))
      = k • (Work.Thom.relCohMap (Work.Whitney.tcmF Y n 1)
            (Work.Whitney.tcmA Y n 1 ∪ Work.Whitney.tcmC Y n 1)
            (Work.Thom.Punct Y (n + 1)) (Work.Whitney.tcmF_mem Y n 1) ℤ (n + 1)).hom
              (Work.Thom.Mpun (n + 1) Y))
    (γ : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))
      (Work.Whitney.tcmA Y n 1 ∪ Work.Whitney.tcmC Y n 1) (n + 1)))
    (hγ : Work.Cohomology.relDiffLM ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))
      (Work.Whitney.tcmA Y n 1 ∪ Work.Whitney.tcmC Y n 1) (n + 1) γ = 0)
    (hγr : Work.Cohomology.relClassOf ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))
      (Work.Whitney.tcmA Y n 1 ∪ Work.Whitney.tcmC Y n 1) γ hγ
      = Work.Whitney.tcmRelCup (Work.Whitney.tcmA Y n 1) (Work.Whitney.tcmC Y n 1)
          (Work.Whitney.isOpen_tcmA Y n 1) (Work.Whitney.isOpen_tcmC Y n 1) n 1
          ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 Y n 1) (Work.Whitney.tcmA Y n 1)
            (Work.Thom.Punct Y n) (fun x hx => hx) ℤ n).hom (Work.Thom.Mpun n Y))
          ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y n 1) (Work.Whitney.tcmC Y n 1)
            (Work.Thom.Punct Y 1) (fun x hx => hx) ℤ 1).hom (Work.Thom.Mpun 1 Y)))
    (s : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) (n + 1)))
    (hs : Work.Cohomology.relDiffLM ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) (n + 1) s = 0)
    (hsr : Work.Cohomology.relClassOf ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) s hs = Work.Thom.Mpun (n + 1) Y)
    (Z : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).X (n + 1))
    (hZ : ∀ ξ : (Work.Whitney.pdABCohR (R := ℤ) (TopCat.of (Work.Whitney.tcmX Y n 1))
        (Work.Whitney.tcmA Y n 1) (Work.Whitney.tcmC Y n 1)).X n,
      Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Work.Whitney.tcmX Y n 1)) ξ.1
        (((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).d (n + 1) n) Z) = 0) :
    Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Work.Whitney.tcmX Y n 1)) γ.1 Z
      = k • Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Work.Whitney.tcmX Y n 1))
          (show Work.Cohomology.Cochain ℤ (Work.Whitney.ssB (Work.Whitney.tcmX Y n 1)) (n + 1) from
            (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))
              (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
              (TopCat.ofHom (Work.Whitney.tcmF Y n 1))).f (n + 1))) s.1) Z := by
  classical
  -- the class of `γ` is `k •` the pullback of the class of `s`
  have hclass : relClassOf ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1) γ hγ
      = k • (Work.Thom.relCohMap (tcmF Y n 1) (tcmA Y n 1 ∪ tcmC Y n 1)
            (Work.Thom.Punct Y (n + 1)) (tcmF_mem Y n 1) ℤ (n + 1)).hom
          (relClassOf ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
            (Work.Thom.Punct Y (n + 1)) s hs) := by
    rw [hγr, h, ← hsr]
  -- naturality of the pullback on classes
  have hnat := homologyMap_relComplexMap_relClassOf (R := ℤ)
      (X₁ := TopCat.of (tcmX Y n 1))
      (X₂ := TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (A₁ := tcmA Y n 1 ∪ tcmC Y n 1) (A₂ := Work.Thom.Punct Y (n + 1))
      (f := TopCat.ofHom (tcmF Y n 1)) (tcmF_mem Y n 1) s hs
  have hpcoc : relDiffLM ℤ (TopCat.of (tcmX Y n 1))
      (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1) (pullRel Y n s) = 0 := pullRel_coc Y n s hs
  have hcr : (Work.Thom.relCohMap (tcmF Y n 1) (tcmA Y n 1 ∪ tcmC Y n 1)
        (Work.Thom.Punct Y (n + 1)) (tcmF_mem Y n 1) ℤ (n + 1)).hom
      (relClassOf ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
        (Work.Thom.Punct Y (n + 1)) s hs)
      = relClassOf ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1)
          (pullRel Y n s) hpcoc := hnat
  have hkpcoc : relDiffLM ℤ (TopCat.of (tcmX Y n 1))
      (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1) (k • pullRel Y n s) = 0 := by
    rw [map_smul, hpcoc, smul_zero]
  have hsm : k • relClassOf ℤ (TopCat.of (tcmX Y n 1))
        (tcmA Y n 1 ∪ tcmC Y n 1) (pullRel Y n s) hpcoc
      = relClassOf ℤ (TopCat.of (tcmX Y n 1))
          (tcmA Y n 1 ∪ tcmC Y n 1) (k • pullRel Y n s) hkpcoc :=
    (relClassOf_smul_local (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1)
      (n + 1) k (pullRel Y n s) hkpcoc hpcoc).symm
  have hclass2 : relClassOf ℤ (TopCat.of (tcmX Y n 1))
        (tcmA Y n 1 ∪ tcmC Y n 1) γ hγ
      = relClassOf ℤ (TopCat.of (tcmX Y n 1))
          (tcmA Y n 1 ∪ tcmC Y n 1) (k • pullRel Y n s) hkpcoc := by
    rw [hclass, hcr, ← hsm]
  -- the pairing only depends on the class
  have hkr := kronecker_eq_of_relClassOf_eq_pdAB (X := TopCat.of (tcmX Y n 1))
    (A := tcmA Y n 1) (C := tcmC Y n 1) n γ (k • pullRel Y n s) hγ hkpcoc hclass2 Z hZ
  rw [hkr]
  rw [show (k • pullRel Y n s).1 = k • (pullRel Y n s).1 from rfl, kronecker_smul, pullRel_coe]

end

end Work.Whitney

#print axioms Work.Whitney.pairClass
#print axioms Work.Whitney.kronecker_eq_of_relClassOf_eq_pdAB
#print axioms Work.Whitney.relClassOf_smul_local
