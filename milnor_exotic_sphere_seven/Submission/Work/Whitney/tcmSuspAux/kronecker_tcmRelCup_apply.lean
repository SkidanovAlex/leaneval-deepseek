import Mathlib
import Submission.Work.Whitney.tcmSuspAux.pairing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The pairing of the relative–relative cup with an `A+C`-cycle

This file instantiates `Work.Whitney.tcmSuspAux.kronecker_tcmRelCup_apply_aux` (the "pairing trick" of
`Submission/Work/Whitney/tcmSuspAux/pairing.lean`) at the two concrete `A+C`-elements

* `e₁ = (pdABInclRelR …).f (n+1) γ`, the image of the representative `γ` of the class
  `tcmRelCup A C hA hC n 1 a b` in the `A+C`-complex, and
* `e₂ = starAB α β`, the Alexander–Whitney product of the representatives `α`, `β` of `a` and `b`,

supplying the three ingredients of the "P1 + P2" of `tcmSuspAux/NOTES_tcmProd_suspRule.md` §2:

* the cocycle conditions (`hγc` from the commutativity of the cochain map `pdABInclRelR`, `hαc` from
  the Leibniz rule `Leibniz3_starAB` and `star3_cocycle_cochain`);
* the equality of the two classes, which is `tcmRelCup_class_eq`;
* the two defining equations of the underlying cochains (`rfl`, `starAB_coe`).
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology

namespace Work.Whitney.tcmSuspAux

theorem kronecker_tcmRelCup_apply {X : Type} [TopologicalSpace X]
    (A C : Set X) (hA : IsOpen A) (hC : IsOpen C)
    (n : ℕ) (a : Work.Thom.RelCoh ℤ n X A) (b : Work.Thom.RelCoh ℤ 1 X C)
    (α : ↥(Work.Cohomology.relKern ℤ (TopCat.of X) A n))
    (hα : Work.Cohomology.relDiffLM ℤ (TopCat.of X) A n α = 0)
    (hαr : Work.Cohomology.relClassOf ℤ (TopCat.of X) A α hα = a)
    (β : ↥(Work.Cohomology.relKern ℤ (TopCat.of X) C 1))
    (hβ : Work.Cohomology.relDiffLM ℤ (TopCat.of X) C 1 β = 0)
    (hβr : Work.Cohomology.relClassOf ℤ (TopCat.of X) C β hβ = b)
    (γ : ↥(Work.Cohomology.relKern ℤ (TopCat.of X) (A ∪ C) (n + 1)))
    (hγ : Work.Cohomology.relDiffLM ℤ (TopCat.of X) (A ∪ C) (n + 1) γ = 0)
    (hγr : Work.Cohomology.relClassOf ℤ (TopCat.of X) (A ∪ C) γ hγ
      = Work.Whitney.tcmRelCup A C hA hC n 1 a b)
    (Z : (Work.Cohomology.singularChains ℤ (TopCat.of X)).X (n + 1))
    (hZ : ∀ ξ : (Work.Whitney.pdABCohR (R := ℤ) (TopCat.of X) A C).X n,
        Work.Cohomology.kronecker ℤ (Work.Whitney.ssB X) ξ.1
          (((Work.Cohomology.singularChains ℤ (TopCat.of X)).d (n + 1) n) Z) = 0) :
    Work.Cohomology.kronecker ℤ (Work.Whitney.ssB X) γ.1 Z
      = Work.Cohomology.kronecker ℤ (Work.Whitney.ssB X)
          (Work.Cohomology.cup ℤ (Work.Whitney.ssB X) α.1 β.1) Z := by
  have hγ' : (ModuleCat.Hom.hom ((relComplex ℤ (TopCat.of X) (A ∪ C)).d (n+1) (n+1+1))) γ = 0 := by
    rw [relComplex_d_apply]; exact hγ
  have hα' : (ModuleCat.Hom.hom ((relComplex ℤ (TopCat.of X) A).d n (n+1))) α = 0 := by
    rw [relComplex_d_apply]; exact hα
  have hβ' : (ModuleCat.Hom.hom ((relComplex ℤ (TopCat.of X) C).d 1 (1+1))) β = 0 := by
    rw [relComplex_d_apply]; exact hβ
  have hγc : (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (n+1) (n+1+1)))
      (ModuleCat.Hom.hom ((pdABInclRelR (TopCat.of X) A C).f (n+1)) γ) = 0 := by
    have hcomm := congrArg (fun g => (ModuleCat.Hom.hom g) γ)
      ((pdABInclRelR (R := ℤ) (TopCat.of X) A C).comm (n+1) (n+1+1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
    rw [hcomm, hγ', map_zero]
  have hαc : (ModuleCat.Hom.hom ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (n+1) (n+1+1)))
      ((starAB (TopCat.of X) A C n 1) α β) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (TopCat.of X) A C) n 1 α β hα' hβ'
  exact kronecker_tcmRelCup_apply_aux A C hA hC n a b α hα hαr β hβ hβr γ hγ hγr
    ((pdABInclRelR (R := ℤ) (TopCat.of X) A C).f (n+1) γ)
    ((starAB (TopCat.of X) A C n 1) α β)
    hγc hαc
    (tcmRelCup_class_eq A C hA hC n a b α hα hαr β hβ hβr γ hγ hγr hγc hαc)
    rfl
    (starAB_coe (R := ℤ) (TopCat.of X) A C n 1 α β)
    Z hZ

end Work.Whitney.tcmSuspAux
