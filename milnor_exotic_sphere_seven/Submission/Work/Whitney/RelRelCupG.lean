import Mathlib
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.RelRelCup
import Submission.Work.Whitney.TautSection
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.exists_unique_pieceClass
import Submission.Work.Thom.MixedCup
import Submission.Work.LerayHirsch.whitneySumFormulaOfLerayHirsch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type} [CommRing R]

/-! ## The canonical relative–relative cup product

`Work.Whitney.relRelCupHMap` is the Alexander–Whitney product on the `A+B` complex
`C^*(X,A) ∩ C^*(X,B)` (`Work.Whitney.starAB`, `Submission/Work/Whitney/RelABComplex.lean`), and it
is *determined* by its value on classes of cocycles (`Work.Whitney.relRelCupHMap_apply`).  The
relative–relative cup is obtained by transporting it to `H^*(X, A∪B)` along the inverse of the
quasi-isomorphism `pdABInclRelR`; we take the *construction* rather than the `Classical.choose` of
`Work.Whitney.exists_relRelCup`, which is what makes the values computable. -/

/-- **The relative–relative cup product, with the transport made explicit.**  For classes
`a ∈ H^m(X,A)`, `b ∈ H^n(X,B)` and any `R`-linear `g` from the cohomology of the `A+B` complex to
`H^{m+n}(X,A∪B)`, this is `g (a ⋆ b)` where `⋆` is the Alexander–Whitney product
(`Work.Whitney.relRelCupHMap`).  The canonical choice of `g` is the inverse of the
quasi-isomorphism `C^*(X,A∪B) → C^*(X,A+B)` (`relRelCupOpen`); any `g` with `φ ∘ g = id` gives the
same values on `a ⋆ b` for the classes of cocycles, which is all the applications use. -/
noncomputable def relRelCupG {X : Type} [TopologicalSpace X] (A B : Set X) (m n : ℕ)
    (g : (pdABCohR (R := R) (TopCat.of X) A B).homology (m + n) →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B)) :
    Work.Thom.RelCoh R m X A →ₗ[R] Work.Thom.RelCoh R n X B →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B) :=
  LinearMap.mk₂ R
    (fun a b => g ((relRelCupHMap (R := R) (TopCat.of X) A B m n) a b))
    (fun a a' b => by simp only [map_add, LinearMap.add_apply])
    (fun c a b => by simp only [map_smul, LinearMap.smul_apply])
    (fun a b b' => by simp only [map_add, LinearMap.add_apply])
    (fun c a b => by simp only [map_smul, LinearMap.smul_apply])

/-- The defining equation of `Work.Whitney.relRelCupG`. -/
theorem relRelCupG_apply {X : Type} [TopologicalSpace X] (A B : Set X) (m n : ℕ)
    (g : (pdABCohR (R := R) (TopCat.of X) A B).homology (m + n) →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B))
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    relRelCupG A B m n g a b
      = g ((relRelCupHMap (R := R) (TopCat.of X) A B m n) a b) :=
  rfl

/-- **THE COMPUTATION RULE of the relative–relative cup product**, from the construction: forgetting
the relative data recovers the Alexander–Whitney product of the two classes.  No openness hypothesis
is needed here — only the gauge-fixing equation `hg` for the transport (which holds for the
canonical choice by `IsIso.inv_hom_id_apply`). -/
theorem relRelCupG_relToAbs {X : Type} [TopologicalSpace X] (A B : Set X) (m n : ℕ)
    (g : (pdABCohR (R := R) (TopCat.of X) A B).homology (m + n) →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B))
    (hg : ∀ y, (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) (m + n)).hom
      (g y) = y)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relToAbs R (A ∪ B) (m + n)).hom (relRelCupG A B m n g a b)
      = Work.Cohomology.cupH' R (ssB X) m n
          ((Work.Thom.relToAbs R A m).hom a) ((Work.Thom.relToAbs R B n).hom b) := by
  change (HomologicalComplex.homologyMap (relIncl R (TopCat.of X) (A ∪ B)) (m + n)).hom
      (g ((relRelCupHMap (R := R) (TopCat.of X) A B m n) a b))
      = cupH' R (ssB X) m n
          ((HomologicalComplex.homologyMap (relIncl R (TopCat.of X) A) m).hom a)
          ((HomologicalComplex.homologyMap (relIncl R (TopCat.of X) B) n).hom b)
  have hrel : (HomologicalComplex.homologyMap (relIncl R (TopCat.of X) (A ∪ B)) (m + n))
      = HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) (m + n)
        ≫ HomologicalComplex.homologyMap (pdABInclL (R := R) (TopCat.of X) A B) (m + n) := by
    rw [← HomologicalComplex.homologyMap_comp, relIncl_eq_pdABInclRelR_comp]
  obtain ⟨α, hα, rfl⟩ := exists_relClassOf R (TopCat.of X) A m a
  obtain ⟨β, hβ, rfl⟩ := exists_relClassOf R (TopCat.of X) B n b
  have hα' : ((relComplex R (TopCat.of X) A).d m (m + 1)).hom α = 0 := by
    rw [relComplex_d_apply]; exact hα
  have hβ' : ((relComplex R (TopCat.of X) B).d n (n + 1)).hom β = 0 := by
    rw [relComplex_d_apply]; exact hβ
  have hstar : ((pdABCohR (R := R) (TopCat.of X) A B).d (m + n) (m + n + 1))
      (starAB (R := R) (TopCat.of X) A B m n α β) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (TopCat.of X) A B) m n α β hα' hβ'
  rw [relIncl_homologyMap_relClassOf R (TopCat.of X) A α hα,
      relIncl_homologyMap_relClassOf R (TopCat.of X) B β hβ]
  rw [cupH'_apply' R (ssB X) α.1 β.1 _ _]
  rw [relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X) A α hα hα',
      relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X) B β hβ hβ']
  rw [relRelCupHMap_apply (R := R) (TopCat.of X) A B m n α β hα' hβ' hstar]
  rw [show (HomologicalComplex.homologyMap (relIncl R (TopCat.of X) (A ∪ B)) (m + n)).hom
        (g (((pdABCohR (R := R) (TopCat.of X) A B).homologyπ (m + n)).hom
          (cocycleOfK (pdABCohR (R := R) (TopCat.of X) A B)
            (starAB (R := R) (TopCat.of X) A B m n α β) hstar)))
      = (HomologicalComplex.homologyMap (pdABInclL (R := R) (TopCat.of X) A B) (m + n)).hom
          (((pdABCohR (R := R) (TopCat.of X) A B).homologyπ (m + n)).hom
            (cocycleOfK (pdABCohR (R := R) (TopCat.of X) A B)
              (starAB (R := R) (TopCat.of X) A B m n α β) hstar)) from by
    rw [hrel]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [hg]]
  rw [pdABInclL_homologyMap_cocycleOfK (TopCat.of X) A B
    (starAB (R := R) (TopCat.of X) A B m n α β) hstar]
  exact cohomologyClassOf_congr R (ssB X)
    (starAB_coe (R := R) (TopCat.of X) A B m n α β) _ _

/-- **The computation rule of the canonical relative--relative cup**, in the form of the interface
`Work.Whitney.relRelCup_relToAbs` (here *proved* from the construction rather than assumed): for
any transport `g` with the gauge-fixing property `hg` (in particular for the canonical one,
`g = (IsIso.inv φ).hom`), the `relToAbs`-image of `a ⌣ b` is the Alexander--Whitney product of
their absolute images. -/
theorem relRelCupCanonical_relToAbs {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (g : (pdABCohR (R := R) (TopCat.of X) A B).homology (m + n) →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B))
    (hg : ∀ y, (HomologicalComplex.homologyMap
        (pdABInclRelR (R := R) (TopCat.of X) A B) (m + n)).hom (g y) = y)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relToAbs R (A ∪ B) (m + n)).hom (relRelCupG A B m n g a b)
      = Work.Cohomology.cupH' R (ssB X) m n
          ((Work.Thom.relToAbs R A m).hom a) ((Work.Thom.relToAbs R B n).hom b) :=
  relRelCupG_relToAbs A B m n g hg a b

end
end Work.Whitney
