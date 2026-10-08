import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.lemma17_iii_aux

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- The restriction to `H₀` of a class function on `G` is invariant under the conjugation
action `ν ↦ ν^s` of `s ∈ H`: this is just the class-function property of `χ` on `G`,
together with `conjMulEquiv P s h = s h s⁻¹`. -/
theorem conjByH_restrict (P : Hyp12 G) (s : ↥P.H) (χ : ClassFunction G ℂ) :
    conjByH P s (ClassFunction.restrict P.H0 χ) = ClassFunction.restrict P.H0 χ := by
  ext h
  rw [conjByH_apply, ClassFunction.restrict_apply, ClassFunction.restrict_apply,
    conjMulEquiv_apply]
  exact χ.conj_eq (h : G) (s : G)

theorem inner_restrict_sconj {G : Type} [Group G] [Finite G]
    (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) :
    OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ)
        (Work.BG.sconj C ν) =
      OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ) ν := by
  have hφ : conjByH C.P C.s⁻¹ (ClassFunction.restrict C.P.H0 χ) =
      ClassFunction.restrict C.P.H0 χ := conjByH_restrict C.P C.s⁻¹ χ
  exact inner_conjByH_eq C.P C.s hφ ν

end Work.BG
