import Mathlib
import Submission.Work.Whitney.cupSide_eval
import Submission.Work.Whitney.pairDeltaC_restr_gammaSharp_eq
import Submission.Work.Whitney.Cutoff

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The cup-side evaluation at the sharp lift (`γt := gammaSharp Y n`)

The instantiation of `Work.Whitney.kronecker_tcmRelCup_eq_cup` (`cupSide_eval.lean`, §55) at the
clever lift: `γt := gammaSharp Y n`, `β := ⟨cochainDiff (gammaSharp Y n), _⟩`, with the two interface
hypotheses discharged by the *proved* facts

* `Work.Whitney.pairDeltaC_restr_gammaSharp_eq` — the transgression of the restriction of `gammaSharp`
  to `tcmC` is `pr2^*(Mpun 1 Y)`;
* `Work.Whitney.pairδC_class_of_lift` (`Cutoff.lean`) — a lift of a `0`-cocycle represents its
  transgression, which converts that into the class of `⟨cochainDiff (gammaSharp Y n), _⟩`;
* `hβeq` is `singularCochain_d_apply` (the two spellings of the dual differential).
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Whitney

open Work.Thom
open Work.Cohomology

noncomputable section

/-- **The cup-side evaluation, at the sharp lift.** -/
theorem kronecker_tcmRelCup_gammaSharp {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (α : ↥(relKern ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) n))
    (hα : relDiffLM ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) n α = 0)
    (hαr : relClassOf ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) α hα
      = (relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom (Mpun n Y))
    (w : ↥(relKern ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1)))
    (hw : relDiffLM ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1) w = 0)
    (hcl : relClassOf ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1) w hw
      = tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
          ((relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom (Mpun n Y))
          ((relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom (Mpun 1 Y)))
    (Z : (singularChains ℤ (TopCat.of (tcmX Y n 1))).X (n + 1))
    (hZ : ∀ ξ : (pdABCohR (R := ℤ) (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) (tcmC Y n 1)).X n,
        kronecker ℤ (ssB (tcmX Y n 1)) ξ.1
          (((singularChains ℤ (TopCat.of (tcmX Y n 1))).d (n + 1) n) Z) = 0) :
    kronecker ℤ (ssB (tcmX Y n 1)) w.1 Z
      = ((-1 : ℤ) ^ n) • kronecker ℤ (ssB (tcmX Y n 1))
          (cup ℤ (ssB (tcmX Y n 1)) α.1 (gammaSharp Y n))
          (((singularChains ℤ (TopCat.of (tcmX Y n 1))).d (n + 1) n) Z) := by
  classical
  obtain ⟨hγ, hgoal⟩ := pairDeltaC_restr_gammaSharp_eq Y n
  obtain ⟨hmem, hcoc, hp⟩ := pairδC_class_of_lift (tcmC Y n 1)
    (((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gammaSharp Y n)) hγ
    (gammaSharp Y n) rfl
  have hβr : relClassOf ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)
      ⟨((singularCochainComplex ℤ (TopCat.of (tcmX Y n 1))).d 0 1).hom (gammaSharp Y n), hmem⟩ hcoc
      = (relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom (Mpun 1 Y) := by
    rw [← hp]
    exact hgoal
  exact kronecker_tcmRelCup_eq_cup (Y := Y) n (gammaSharp Y n) α hα hαr
    ⟨((singularCochainComplex ℤ (TopCat.of (tcmX Y n 1))).d 0 1).hom (gammaSharp Y n), hmem⟩
    hcoc hβr
    (singularCochain_d_apply ℤ (TopCat.of (tcmX Y n 1)) (gammaSharp Y n))
    w hw hcl Z hZ

end

end Work.Whitney

#print axioms Work.Whitney.kronecker_tcmRelCup_gammaSharp
