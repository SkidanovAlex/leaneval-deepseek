import Mathlib
import Submission.Work.Whitney.TCMQDefs
import Submission.Work.Whitney.TripleRel
import Submission.Work.Whitney.pd3InclRelR_quasiIso
import Submission.Work.Whitney.tcmRelCup_tripleImage_agree
import Submission.Work.Whitney.tcmRelCup_tripleImage_agreeA
import Submission.Work.Whitney.tcmRelCupAssocAux
import Submission.Work.Whitney.tcmRelCup_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-
# Associativity of the canonical relative–relative cup product

The canonical relative–relative cup product `Work.Whitney.tcmRelCup` is the Alexander–Whitney
product on the `A+B` complex `C^*(X,A) ∩ C^*(X,B)`, transported along the inverse of the
quasi-isomorphism `C^*(X,A∪B) → C^*(X,A+B)`.  This module proves its associativity.

Both bracketings of the triple product are compared inside the three-fold intersection complex
`C^*(X,A+B+C)` (`Work.Whitney.pd3CohR`), where the comparison is the proved lemma
`Work.Whitney.tcmRelCup_tripleImage_agreeA`; the injectivity of
`C^*(X,A∪B∪C) → C^*(X,A+B+C)` (`Work.Whitney.pd3InclRelR_quasiIso`) then gives the result.  The
`Set.union_assoc` transport between `(A∪B)∪C` and `A∪(B∪C)` is handled through the *generalised*
inclusion `pd3InclRelROf` (whose target set is a variable, so that `cases` applies).
-/

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The inclusion `C^*(X,T) → C^*(X,A+B+C)`** for a set `T` containing `A`, `B` and `C`
(a generalisation of `Work.Whitney.pd3InclRelR`, whose target set is `(A∪B)∪C`). -/
def pd3InclRelROf (A B C T : Set X) (hA : A ⊆ T) (hB : B ⊆ T) (hC : C ⊆ T) :
    relComplex ℤ (TopCat.of X) T ⟶ pd3CohR (TopCat.of X) A B C :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion
      (le_inf (le_inf (relKern_mono hA) (relKern_mono hB)) (relKern_mono hC))))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        relComplex_d, pd3CohR_d]
      rfl)

/-- The generalised inclusion agrees with `pd3InclRelR` on `T = (A∪B)∪C`. -/
lemma pd3InclRelROf_eq_pd3InclRelR (A B C : Set X) (hA : A ⊆ (A ∪ B) ∪ C)
    (hB : B ⊆ (A ∪ B) ∪ C) (hC : C ⊆ (A ∪ B) ∪ C) :
    pd3InclRelROf A B C ((A ∪ B) ∪ C) hA hB hC = pd3InclRelR (TopCat.of X) A B C := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  rfl

/-- **The transport of the generalised inclusion**: transporting a class along an equality of the
underlying sets does not change its image (both maps are the inclusion of the same submodules). -/
lemma pd3InclRelROf_transport {S T : Set X} (h : S = T) (A B C : Set X)
    (hAS : A ⊆ S) (hBS : B ⊆ S) (hCS : C ⊆ S) (hAT : A ⊆ T) (hBT : B ⊆ T) (hCT : C ⊆ T)
    (n : ℕ) (x : (relComplex ℤ (TopCat.of X) S).homology n) :
    (HomologicalComplex.homologyMap (pd3InclRelROf A B C T hAT hBT hCT) n).hom (h ▸ x)
      = (HomologicalComplex.homologyMap (pd3InclRelROf A B C S hAS hBS hCS) n).hom x := by
  cases h
  congr 1

/-- The generalised inclusion composed with a canonical cup, in the two-fold form. -/
lemma pd3InclRelROf_cup (A B C : Set X) (hA : A ⊆ (A ∪ B) ∪ C) (hB : B ⊆ (A ∪ B) ∪ C)
    (hC : C ⊆ (A ∪ B) ∪ C) (n : ℕ) :
    pd3InclRelROf A B C ((A ∪ B) ∪ C) hA hB hC
      = pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C ≫
        pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C := by
  rw [pd3InclRelROf_eq_pd3InclRelR A B C hA hB hC]
  exact pd3InclRelR_factor_left_cm A B C

/-- The mirror of `pd3InclRelROf_cup` for `T = A ∪ (B ∪ C)`. -/
lemma pd3InclRelROf_cup' (A B C : Set X) (hA : A ⊆ A ∪ (B ∪ C)) (hB : B ⊆ A ∪ (B ∪ C))
    (hC : C ⊆ A ∪ (B ∪ C)) :
    pd3InclRelROf A B C (A ∪ (B ∪ C)) hA hB hC
      = pdABInclRelR (R := ℤ) (TopCat.of X) A (B ∪ C) ≫
        pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  rfl

/-- The degree and set transports of a class commute (specialised to `RelCoh`, so that the
rewriting below matches syntactically). -/
lemma eqRec_swapRel {S T : Set X} (hS : S = T) {m m' : ℕ} (hn : m = m')
    (x : Work.Thom.RelCoh ℤ m X S) :
    hn ▸ (hS ▸ x) = hS ▸ (hn ▸ x) := by
  cases hS
  cases hn
  rfl

/-- `h ▸ (h.symm ▸ x) = x` for classes (transport by an equality of sets). -/
lemma eqRec_symm_self {S T : Set X} (h : S = T) (n : ℕ)
    (x : (relComplex ℤ (TopCat.of X) T).homology n) : h ▸ (h.symm ▸ x) = x := by
  cases h
  rfl

/-- `h.symm ▸ (h ▸ x) = x` for classes (transport by an equality of sets). -/
lemma eqRec_self_symm {S T : Set X} (h : S = T) (n : ℕ)
    (x : (relComplex ℤ (TopCat.of X) S).homology n) : h.symm ▸ (h ▸ x) = x := by
  cases h
  rfl

/-- Transporting by `h.symm` is injective. -/
lemma eqRec_symm_inj {S T : Set X} (h : S = T) (n : ℕ) :
    Function.Injective (fun x : (relComplex ℤ (TopCat.of X) T).homology n => h.symm ▸ x) := by
  intro x y hxy
  have h' := congrArg (fun z => h ▸ z) hxy
  rwa [eqRec_symm_self h n x, eqRec_symm_self h n y] at h'


/-- **The image of a class of `C^*(X,(A∪B)∪C)` under the structural inclusion**, computed
through the pair `(A∪B, C)`, with the degree transport made explicit.  This is the cohomology-level
form of `Work.Whitney.pd3InclRelR_factor_left_cm` combined with the transport
`Work.Whitney.eqRec_homologyMap`. -/
lemma pd3InclRelR_image_left (A B C : Set X) {m m' : ℕ} (h : m = m')
    (x : Work.Thom.RelCoh ℤ m X ((A ∪ B) ∪ C)) :
    (HomologicalComplex.homologyMap (pd3InclRelR (TopCat.of X) A B C) m').hom (h ▸ x)
      = h ▸ ((HomologicalComplex.homologyMap
            (pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C) m).hom
          ((HomologicalComplex.homologyMap
            (pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C) m).hom x)) := by
  rw [pd3InclRelR_factor_left_cm, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [← eqRec_homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C) h x]
  rw [← eqRec_homologyMap (pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C) h
    ((HomologicalComplex.homologyMap
      (pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C) m).hom x)]

/-- **The image of a class of `C^*(X,A∪(B∪C))` under the structural inclusion**, transported
along `h : A∪(B∪C) = (A∪B)∪C` to the source of `pd3InclRelR` and computed through the pair
`(A, B∪C)`.  This is `Work.Whitney.pd3InclRelROf_transport` combined with the factorisation
`Work.Whitney.pd3InclRelROf_cup'`. -/
lemma pd3InclRelR_image_right (A B C : Set X) (p q r : ℕ)
    (h : A ∪ (B ∪ C) = (A ∪ B) ∪ C)
    (x : Work.Thom.RelCoh ℤ (p + (q + r)) X (A ∪ (B ∪ C))) :
    (HomologicalComplex.homologyMap
        (pd3InclRelROf A B C ((A ∪ B) ∪ C) (fun y hy => Or.inl (Or.inl hy))
          (fun y hy => Or.inl (Or.inr hy)) (fun y hy => Or.inr hy)) (p + (q + r))).hom (h ▸ x)
      = (HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C)
          (p + (q + r))).hom
        ((HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) A (B ∪ C))
          (p + (q + r))).hom x) := by
  rw [pd3InclRelROf_transport h A B C
    (fun y hy => Or.inl hy) (fun y hy => Or.inr (Or.inl hy)) (fun y hy => Or.inr (Or.inr hy))
    (fun y hy => Or.inl (Or.inl hy)) (fun y hy => Or.inl (Or.inr hy)) (fun y hy => Or.inr hy)
    (p + (q + r)) x]
  rw [pd3InclRelROf_cup' A B C (fun y hy => Or.inl hy) (fun y hy => Or.inr (Or.inl hy))
    (fun y hy => Or.inr (Or.inr hy))]
  rw [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

end

end Work.Whitney
