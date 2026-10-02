import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.RelABComplex
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Cohomology.pd_us_ab_resolve

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The pairing trick for the `A+B` complex

Two `A+B`-cocycles of the same cohomology class have equal Kronecker pairings with any chain `Z`
whose boundary is annihilated by *every* `A+B`-cochain (`∂Z` is a sum of simplices each contained
in `A` or in `C`).  This is the well-definedness of the evaluation of an `A+B`-class on an
`A+B`-cycle, and it is what makes the "cut-off class" of the relative–relative cup computable
*without* the (non-explicit) inverse of the quasi-isomorphism `C^*(X,A∪B) → C^*(X,A+B)`.

It is the hypothesis-`hZ` form of `Work.Whitney.RankTwo.exists_pdABDiff_of_class_eq` +
`Work.Cohomology.kronecker_cocycle_boundary`, generalised to arbitrary `A`, `C` and degrees; see
`tcmSuspAux/NOTES_tcmProd_suspRule.md` §2 (P1).
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology

namespace Work.Whitney.tcmSuspAux

noncomputable section

/-- **The pairing trick**: the Kronecker pairing of an `A+C`-cohomology class with a chain whose
boundary is an `A+C`-chain is computed by any representative. -/
theorem kronecker_pdABCohR_eq_of_homology_eq {X : TopCat} (A C : Set X) (k : ℕ)
    (γ γ' : (pdABCohR (R := ℤ) X A C).X (k + 1))
    (hγ : ((pdABCohR (R := ℤ) X A C).d (k + 1) (k + 1 + 1)) γ = 0)
    (hγ' : ((pdABCohR (R := ℤ) X A C).d (k + 1) (k + 1 + 1)) γ' = 0)
    (h : ((pdABCohR (R := ℤ) X A C).homologyπ (k + 1))
          (cocycleOfK (pdABCohR (R := ℤ) X A C) γ hγ)
        = ((pdABCohR (R := ℤ) X A C).homologyπ (k + 1))
          (cocycleOfK (pdABCohR (R := ℤ) X A C) γ' hγ'))
    (Z : (singularChains ℤ X).X (k + 1))
    (hZ : ∀ ξ : (pdABCohR (R := ℤ) X A C).X k,
        kronecker ℤ (ssB X) ξ.1 (((singularChains ℤ X).d (k + 1) k) Z) = 0) :
    kronecker ℤ (ssB X) γ.1 Z = kronecker ℤ (ssB X) γ'.1 Z := by
  classical
  -- the difference is a cycle
  have hd : ((pdABCohR (R := ℤ) X A C).d (k + 1) (k + 1 + 1)) (γ - γ') = 0 := by
    rw [map_sub, hγ, hγ', sub_self]
  -- and its class vanishes
  have hcyc : cocycleOfK (pdABCohR (R := ℤ) X A C) (γ - γ') hd
      = cocycleOfK (pdABCohR (R := ℤ) X A C) γ hγ
        - cocycleOfK (pdABCohR (R := ℤ) X A C) γ' hγ' := by
    apply (ModuleCat.mono_iff_injective
      ((pdABCohR (R := ℤ) X A C).iCycles (k + 1))).mp inferInstance
    rw [map_sub, iCycles_cocycleOfK, iCycles_cocycleOfK, iCycles_cocycleOfK]
  have hzero : ((pdABCohR (R := ℤ) X A C).homologyπ (k + 1))
      (cocycleOfK (pdABCohR (R := ℤ) X A C) (γ - γ') hd) = 0 := by
    rw [hcyc, map_sub, h, sub_self]
  -- hence it is a coboundary
  obtain ⟨η, hη⟩ := pd_us_ab_resolve_exists_of_homologyπ_eq_zero
    (pdABCohR (R := ℤ) X A C) k _ hzero
  have hη' : γ - γ' = ((pdABCohR (R := ℤ) X A C).d k (k + 1)) η := by
    rw [hη, iCycles_cocycleOfK]
  -- evaluate
  have heval : kronecker ℤ (ssB X) (γ.1 - γ'.1) Z = 0 := by
    have hcoe : (γ.1 - γ'.1 : Cochain ℤ (ssB X) (k + 1))
        = cochainDiff ℤ (ssB X) η.1 := by
      have h2 : ((γ - γ').1 : Cochain ℤ (ssB X) (k + 1))
          = (((pdABCohR (R := ℤ) X A C).d k (k + 1)) η).1 := congrArg Subtype.val hη'
      rw [show (γ.1 - γ'.1 : Cochain ℤ (ssB X) (k + 1)) = (γ - γ').1 from rfl]
      rw [h2, pdABCohR_d_coe, singularCochain_d_apply]
    rw [hcoe]
    exact hZ η
  have hsub : kronecker ℤ (ssB X) γ.1 Z - kronecker ℤ (ssB X) γ'.1 Z = 0 := by
    rw [← heval]
    rfl
  exact sub_eq_zero.mp hsub

/-- The class of a morphism of cochain complexes on `homologyπ` of a cycle. -/
theorem homologyπ_cyclesMap {C D : CochainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (i : ℕ)
    (z : C.cycles i) :
    (ConcreteCategory.hom (HomologicalComplex.homologyMap φ i))
        ((ConcreteCategory.hom (HomologicalComplex.homologyπ C i)) z)
      = (ConcreteCategory.hom (HomologicalComplex.homologyπ D i))
        ((ConcreteCategory.hom (HomologicalComplex.cyclesMap φ i)) z) := by
  have h2 := congrArg (fun (g : C.cycles i ⟶ D.homology i) => g.hom z)
    (HomologicalComplex.homologyπ_naturality φ i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2


/-- `cocycleOfK` of the image of a cocycle under a map of cochain complexes is the image under
`cyclesMap` of the cycle. -/
theorem cocycleOfK_cyclesMap {C D : CochainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (i : ℕ)
    (γ : C.X i) (h : (ModuleCat.Hom.hom (C.d i (i + 1))) γ = 0)
    (h' : (ModuleCat.Hom.hom (D.d i (i + 1))) ((ModuleCat.Hom.hom (φ.f i)) γ) = 0) :
    cocycleOfK D ((ModuleCat.Hom.hom (φ.f i)) γ) h'
      = (ModuleCat.Hom.hom (HomologicalComplex.cyclesMap φ i)) (cocycleOfK C γ h) := by
  apply (ModuleCat.mono_iff_injective (D.iCycles i)).mp inferInstance
  rw [iCycles_cocycleOfK]
  have h2 := congrArg (fun (g : C.cycles i ⟶ D.X i) =>
    (ModuleCat.Hom.hom g) (cocycleOfK C γ h)) (HomologicalComplex.cyclesMap_i φ i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact (h2.trans (congrArg (fun z => (ModuleCat.Hom.hom (φ.f i)) z)
    (iCycles_cocycleOfK C γ h))).symm

/-- The gauge equation of the canonical relative–relative cup, in terms of `homologyMap` (a local
copy of `Work.Whitney.tcmRelCup_gauge`, whose module is not needed here). -/
theorem tcmRelCup_gauge' {X : Type} [TopologicalSpace X] (A C : Set X) (hA : IsOpen A)
    (hC : IsOpen C) (n : ℕ) (a : Work.Thom.RelCoh ℤ n X A) (b : Work.Thom.RelCoh ℤ 1 X C) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (pdABInclRelR (TopCat.of X) A C) (n + 1))) (tcmRelCup A C hA hC n 1 a b)
      = ((relRelCupHMap (TopCat.of X) A C n 1) a) b := by
  rw [show tcmRelCup A C hA hC n 1 a b
      = tcmRelCupG A C n 1 (tcmRelCupInv A C hA hC (n + 1)) a b from rfl]
  rw [tcmRelCupG_apply, tcmRelCupInv_spec]

/-- **The `A+C`-class of the relative–relative cup is the class of the Alexander–Whitney product**
of the representatives, in the form of `homologyπ (cocycleOfK ·)`.  This is the class-level input of
`kronecker_tcmRelCup_apply` (see `tcmSuspAux/NOTES_tcmProd_suspRule.md` §2). -/
theorem tcmRelCup_class_eq {X : Type} [TopologicalSpace X] (A C : Set X) (hA : IsOpen A)
    (hC : IsOpen C) (n : ℕ)
    (a : Work.Thom.RelCoh ℤ n X A) (b : Work.Thom.RelCoh ℤ 1 X C)
    (α : ↥(relKern ℤ (TopCat.of X) A n)) (hα : relDiffLM ℤ (TopCat.of X) A n α = 0)
    (hαr : relClassOf ℤ (TopCat.of X) A α hα = a)
    (β : ↥(relKern ℤ (TopCat.of X) C 1)) (hβ : relDiffLM ℤ (TopCat.of X) C 1 β = 0)
    (hβr : relClassOf ℤ (TopCat.of X) C β hβ = b)
    (γ : ↥(relKern ℤ (TopCat.of X) (A ∪ C) (n + 1)))
    (hγ : relDiffLM ℤ (TopCat.of X) (A ∪ C) (n + 1) γ = 0)
    (hγr : relClassOf ℤ (TopCat.of X) (A ∪ C) γ hγ = tcmRelCup A C hA hC n 1 a b)
    (hγc : (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (n + 1) (n + 1 + 1)))
      ((ModuleCat.Hom.hom ((pdABInclRelR (TopCat.of X) A C).f (n + 1))) γ) = 0)
    (hαc : (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (n + 1) (n + 1 + 1)))
      ((starAB (TopCat.of X) A C n 1) α β) = 0) :
    (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).homologyπ (n + 1)))
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C)
          ((ModuleCat.Hom.hom ((pdABInclRelR (TopCat.of X) A C).f (n + 1))) γ) hγc)
      = (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).homologyπ (n + 1)))
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C)
          ((starAB (TopCat.of X) A C n 1) α β) hαc) := by
  classical
  have hαabs : (ModuleCat.Hom.hom ((relComplex ℤ (TopCat.of X) A).d n (n + 1))) α = 0 := by
    rw [relComplex_d_apply]; exact hα
  have hβabs : (ModuleCat.Hom.hom ((relComplex ℤ (TopCat.of X) C).d 1 (1 + 1))) β = 0 := by
    rw [relComplex_d_apply]; exact hβ
  have hγrel : (ModuleCat.Hom.hom
      ((relComplex ℤ (TopCat.of X) (A ∪ C)).d (n + 1) (n + 1 + 1))) γ = 0 := by
    rw [relComplex_d_apply]; exact hγ
  rw [cocycleOfK_cyclesMap (pdABInclRelR (TopCat.of X) A C) (n + 1) γ hγrel hγc]
  rw [← homologyπ_cyclesMap (pdABInclRelR (TopCat.of X) A C) (n + 1)
    (cocycleOfK (relComplex ℤ (TopCat.of X) (A ∪ C)) γ hγrel)]
  rw [← relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) (A ∪ C) γ hγ hγrel]
  rw [hγr, tcmRelCup_gauge' A C hA hC n a b]
  rw [← hαr, ← hβr]
  rw [relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) A α hα hαabs]
  rw [relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) C β hβ hβabs]
  exact relRelCupHMap_apply (TopCat.of X) A C n 1 α β hαabs hβabs hαc


/-- **The pairing of the relative–relative cup with an `A+C`-cycle**: with the two `A+C`-elements
`e₁` (the image of the representative `γ` of `tcmRelCup A C a b` in the `A+C` complex) and `e₂`
(the Alexander–Whitney product `starAB α β`) and the hypothesis that their `A+C`-classes agree, the
pairing of `γ` with `Z` is the pairing of `α ⌣ β` with `Z`.  This is the form of
`kronecker_tcmRelCup_apply` in which the two elements are hypotheses (so that the defeq checks
against the unfolded `pdABInclRelR`-terms stay cheap); the geometric input of the suspension rule is
the chain `Z` and its `hZ` property. -/
theorem kronecker_tcmRelCup_apply_aux {X : Type} [TopologicalSpace X] (A C : Set X) (hA : IsOpen A)
    (hC : IsOpen C) (n : ℕ)
    (a : Work.Thom.RelCoh ℤ n X A) (b : Work.Thom.RelCoh ℤ 1 X C)
    (α : ↥(relKern ℤ (TopCat.of X) A n)) (hα : relDiffLM ℤ (TopCat.of X) A n α = 0)
    (hαr : relClassOf ℤ (TopCat.of X) A α hα = a)
    (β : ↥(relKern ℤ (TopCat.of X) C 1)) (hβ : relDiffLM ℤ (TopCat.of X) C 1 β = 0)
    (hβr : relClassOf ℤ (TopCat.of X) C β hβ = b)
    (γ : ↥(relKern ℤ (TopCat.of X) (A ∪ C) (n + 1)))
    (hγ : relDiffLM ℤ (TopCat.of X) (A ∪ C) (n + 1) γ = 0)
    (hγr : relClassOf ℤ (TopCat.of X) (A ∪ C) γ hγ = tcmRelCup A C hA hC n 1 a b)
    (e₁ : (pdABCohR (R := ℤ) (TopCat.of X) A C).X (n + 1))
    (e₂ : (pdABCohR (R := ℤ) (TopCat.of X) A C).X (n + 1))
    (hγc : (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (n + 1) (n + 1 + 1)))
      e₁ = 0)
    (hαc : (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (n + 1) (n + 1 + 1)))
      e₂ = 0)
    (hcl : (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).homologyπ (n + 1)))
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) e₁ hγc)
      = (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).homologyπ (n + 1)))
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) e₂ hαc))
    (he₁ : e₁.1 = γ.1) (he₂ : e₂.1 = cup ℤ (ssB X) α.1 β.1)
    (Z : (singularChains ℤ (TopCat.of X)).X (n + 1))
    (hZ : ∀ ξ : (pdABCohR (R := ℤ) (TopCat.of X) A C).X n,
        kronecker ℤ (ssB X) ξ.1 (((singularChains ℤ (TopCat.of X)).d (n + 1) n) Z) = 0) :
    kronecker ℤ (ssB X) γ.1 Z
      = kronecker ℤ (ssB X) (cup ℤ (ssB X) α.1 β.1) Z := by
  have hp : kronecker ℤ (ssB X) e₁.1 Z = kronecker ℤ (ssB X) e₂.1 Z :=
    kronecker_pdABCohR_eq_of_homology_eq (X := TopCat.of X) A C n e₁ e₂ hγc hαc hcl Z hZ
  rw [he₁] at hp
  rw [he₂] at hp
  exact hp

end

end Work.Whitney.tcmSuspAux


