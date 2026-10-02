import Mathlib
import Submission.Work.StemsB.wangCollarDerivDefs
import Submission.Work.StemsB.pairDelta_relComplexMap
import Submission.Work.StemsB.FibrewiseTrivIso
import Submission.Work.Cohomology.hmv_naturality
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.StemsB

noncomputable section

/-- **Step A.** The relative cochain map of a pair map is an isomorphism on cohomology as soon as
the underlying relative chain map is a quasi-isomorphism.  This is the transport of the
quasi-isomorphism across the duality `C^*(X,A) ≅ Hom(C_*(X,A),ℤ)`
(`Work.Cohomology.hmvRelComplexMap_comp_inv` + `Work.Cohomology.dualComplexMap_quasiIso`). -/
theorem isIso_homologyMap_relComplexMap_of_pairsChains {X₁ X₂ : TopCat} (A₁ : Set X₁)
    (A₂ : Set X₂) (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂)
    (hψ : ∀ n, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.hmvPairsChains A₁ A₂ f h) n)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ A₁ A₂ f h) n) := by
  have hcomp : HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ A₁ A₂ f h) n ≫
        HomologicalComplex.homologyMap (Work.Cohomology.relDualIsoComplex X₁ A₁).inv n
      = HomologicalComplex.homologyMap (Work.Cohomology.relDualIsoComplex X₂ A₂).inv n ≫
        HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap ℤ
          (Work.Cohomology.relChains X₁ A₁) (Work.Cohomology.relChains X₂ A₂)
          (Work.Cohomology.hmvPairsChains A₁ A₂ f h)) n := by
    rw [← HomologicalComplex.homologyMap_comp,
      Work.Cohomology.hmvRelComplexMap_comp_inv A₁ A₂ f h,
      HomologicalComplex.homologyMap_comp]
  have hd : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap ℤ
      (Work.Cohomology.relChains X₁ A₁) (Work.Cohomology.relChains X₂ A₂)
      (Work.Cohomology.hmvPairsChains A₁ A₂ f h)) n) :=
    Work.Cohomology.dualComplexMap_quasiIso _ (fun k => Work.Cohomology.relChainsProjective X₁ A₁ k)
      (fun k => Work.Cohomology.relChainsProjective X₂ A₂ k) hψ n
  have he : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relDualIsoComplex X₂ A₂).inv n) :=
    inferInstance
  have hR : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relDualIsoComplex X₂ A₂).inv n ≫
      HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap ℤ
        (Work.Cohomology.relChains X₁ A₁) (Work.Cohomology.relChains X₂ A₂)
        (Work.Cohomology.hmvPairsChains A₁ A₂ f h)) n) := inferInstance
  have hce : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ A₁ A₂ f h) n ≫
      HomologicalComplex.homologyMap (Work.Cohomology.relDualIsoComplex X₁ A₁).inv n) :=
    hcomp ▸ hR
  exact IsIso.of_isIso_comp_right
    (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ A₁ A₂ f h) n)
    (HomologicalComplex.homologyMap (Work.Cohomology.relDualIsoComplex X₁ A₁).inv n)

/-- **Step B.** Excision in the form needed here: for open `U, A ⊆ X` with `U ∪ A = X`, the
relative chain map of the inclusion `(U, U∩A) → (X,A)` is a quasi-isomorphism
(`Work.Cohomology.excision_relChainsMap_isIso`), and it agrees with the pair map of the
inclusion. -/
theorem isIso_hmvPairsChains_excision (X : TopCat) (U A : Set X) (hU : IsOpen U) (hA : IsOpen A)
    (hcov : U ∪ A = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.hmvPairsChains
      (X₁ := TopCat.of U) (X₂ := X) {y : ↥U | (y : X) ∈ A} A
      (Work.Cohomology.subtypeIncl X U) (fun x hx => hx)) n) := by
  have hg : Work.Cohomology.hmvPairsChains (X₁ := TopCat.of U) (X₂ := X)
      {y : ↥U | (y : X) ∈ A} A (Work.Cohomology.subtypeIncl X U) (fun x hx => hx)
      = Work.Cohomology.relChainsMap X U A := rfl
  rw [hg]
  exact Work.Cohomology.excision_relChainsMap_isIso X U A hU hA hcov n

/-- **Step C.** Cohomological excision for an open cover of `X`, read on the cochain level: the
relative cochain map of the inclusion `(U, U∩A) → (X,A)` is an isomorphism on cohomology. -/
theorem isIso_relComplexMap_of_open_cover (X : TopCat) (U A : Set X) (hU : IsOpen U) (hA : IsOpen A)
    (hcov : U ∪ A = Set.univ) (A₁ : Set ↥U) (hA₁ : A₁ = {y : ↥U | (y : X) ∈ A})
    (h : ∀ x ∈ A₁, (Work.Cohomology.subtypeIncl X U) x ∈ A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ
      (X₁ := TopCat.of U) (X₂ := X) A₁ A (Work.Cohomology.subtypeIncl X U) h) n) := by
  subst hA₁
  refine isIso_homologyMap_relComplexMap_of_pairsChains _ A _ h (fun n => ?_) n
  rw [Subsingleton.elim h (fun x hx => hx)]
  exact isIso_hmvPairsChains_excision X U A hU hA hcov n

theorem wangExc_isIso (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (k : ℕ) :
    CategoryTheory.IsIso (Work.StemsB.wangExc b p k) := by
  have hsp : wangA1 b p = ({y : ↥(p ⁻¹' sphLoopBig b) | (y : E) ∈ p ⁻¹' sphLoopOuter b}) := by
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, x.2⟩
  have hcov : p ⁻¹' sphLoopBig b ∪ p ⁻¹' sphLoopOuter b = Set.univ := by
    rw [← Set.preimage_union, Set.union_comm, sphLoopOuter_union_sphLoopBig, Set.preimage_univ]
  exact isIso_relComplexMap_of_open_cover (TopCat.of E) (p ⁻¹' sphLoopBig b)
    (p ⁻¹' sphLoopOuter b)
    ((sphLoopBig_open b).preimage p.continuous) ((sphLoopOuter_open b).preimage p.continuous)
    hcov (wangA1 b p) hsp (wangExcMap_mem b p) k

end

end Work.StemsB
