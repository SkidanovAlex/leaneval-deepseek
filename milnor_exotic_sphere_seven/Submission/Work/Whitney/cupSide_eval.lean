import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.Cutoff
import Submission.Work.Whitney.capTransferPrep
import Submission.Work.Whitney.tcmSuspAux.kronecker_tcmRelCup_apply
import Submission.Work.Whitney.kronCochainDiff

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The cup-side evaluation of the rank-one model product formula

The rewriting backbone of `rankOne_cup_model_NOTES.md` §51/§53/§54b.  For a `0`-cochain `γt` (in
practice `gammaSharp Y n`), a cocycle `w` representing the relative–relative cup and a chain `Z`
whose boundary is annihilated by the `A+C`-cochains,

    ⟨w.1, Z⟩ = (-1)^n ⟨α ⌣ γt, ∂Z⟩

Every ingredient is proved in the tree (`tcmSuspAux.kronecker_tcmRelCup_apply`,
`cup_cochainDiff_leibniz`, `relClassOf_cochainDiff`, Stokes by `rfl`); the hypotheses `hαr`, `hβr`,
`hβeq` are the interface to `pairDeltaC_restr_gammaSharp_eq` + `pairδC_class_of_lift` (§53).

**Spelling note (§54b).**  `γt` is a *variable* here, not the term `gammaSharp Y n`: with `γt` a
variable its degree is a known `0`, so `cochainDiff`'s implicit `{n}` resolves, whereas writing
`gammaSharp Y n` inline made `{n}` inferable from two sides that agree only up to the `Cochain`
abbreviation.  This is §42h's rule in its statement form.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Whitney

open Work.Thom
open Work.Cohomology

noncomputable section

/-- **The cup-side evaluation.** -/
theorem kronecker_tcmRelCup_eq_cup {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (γt : Cochain ℤ (ssB (tcmX Y n 1)) 0)
    (α : ↥(relKern ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) n))
    (hα : relDiffLM ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) n α = 0)
    (hαr : relClassOf ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) α hα
      = (Work.Thom.relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom (Mpun n Y))
    (β : ↥(relKern ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1) 1))
    (hβ : relDiffLM ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1) 1 β = 0)
    (hβr : relClassOf ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1) β hβ
      = (Work.Thom.relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom (Mpun 1 Y))
    (hβeq : β.1 = cochainDiff ℤ (ssB (tcmX Y n 1)) γt)
    (w : ↥(relKern ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1)))
    (hw : relDiffLM ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1) (n + 1) w = 0)
    (hcl : relClassOf ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1 ∪ tcmC Y n 1) w hw
      = tcmRelCup (tcmA Y n 1) (tcmC Y n 1) (isOpen_tcmA Y n 1) (isOpen_tcmC Y n 1) n 1
          ((Work.Thom.relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom (Mpun n Y))
          ((Work.Thom.relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom (Mpun 1 Y)))
    (Z : (singularChains ℤ (TopCat.of (tcmX Y n 1))).X (n + 1))
    (hZ : ∀ ξ : (pdABCohR (R := ℤ) (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) (tcmC Y n 1)).X n,
        kronecker ℤ (ssB (tcmX Y n 1)) ξ.1
          (((singularChains ℤ (TopCat.of (tcmX Y n 1))).d (n + 1) n) Z) = 0) :
    kronecker ℤ (ssB (tcmX Y n 1)) w.1 Z
      = ((-1 : ℤ) ^ n) • kronecker ℤ (ssB (tcmX Y n 1))
          (cup ℤ (ssB (tcmX Y n 1)) α.1 γt)
          (((singularChains ℤ (TopCat.of (tcmX Y n 1))).d (n + 1) n) Z) := by
  classical
  have hpair := Work.Whitney.tcmSuspAux.kronecker_tcmRelCup_apply
    (X := tcmX Y n 1)
    (A := tcmA Y n 1) (C := tcmC Y n 1)
    (hA := isOpen_tcmA Y n 1) (hC := isOpen_tcmC Y n 1) (n := n)
    (a := (Work.Thom.relCohMap (tcmPr1 Y n 1) (tcmA Y n 1) (Punct Y n) (fun x hx => hx) ℤ n).hom
      (Mpun n Y))
    (b := (Work.Thom.relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom
      (Mpun 1 Y))
    (α := α) (hα := hα) (hαr := hαr) (β := β) (hβ := hβ) (hβr := hβr)
    (γ := w) (hγ := hw) (hγr := hcl) (Z := Z) (hZ := hZ)
  rw [hpair, hβeq]
  have hαc : cochainDiff ℤ (ssB (tcmX Y n 1)) α.1 = 0 :=
    relClassOf_cochainDiff ℤ (TopCat.of (tcmX Y n 1)) (tcmA Y n 1) α hα
  rw [cup_cochainDiff_leibniz (R := ℤ) (ssB (tcmX Y n 1)) α.1 hαc γt]
  rw [kronecker_smul, kronecker_cochainDiff]
  rfl

end

end Work.Whitney

#print axioms Work.Whitney.kronecker_tcmRelCup_eq_cup
