import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lambda
import Submission.Work.BG.s02_lemma17T_aux

namespace Work.BG

theorem s02_lemma17T_sumTwist {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0)]
    (β : Work.BG.quotGroup C.P →* ℂˣ)
    (a : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ → ℂ) (g : ↥C.P.H0)
    (ha : ∀ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        a (Work.BG.lamTwist C β ν) = a ν) :
    (∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        a ν * (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g)
      = Work.BG.lamCF C β g *
        (∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        a ν * (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g) := by
  classical
  -- The twist `ν ↦ λ_β · ν` is a bijection of `Irr(H₀)`, so the sum may be reindexed by it;
  -- invariance of `a` under the twist turns the reindexed sum into `λ_β(g) · S`.
  have h1 : (∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        a (Work.BG.lamTwist C β ν) *
          (Work.BG.lamTwist C β ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g)
      = ∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        a ν * (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g :=
    Fintype.sum_bijective (Work.BG.lamTwist C β) (Work.BG.lamTwist_bijective C β) _ _
      (fun _ => rfl)
  calc (∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        a ν * (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g)
      = ∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        a (Work.BG.lamTwist C β ν) *
          (Work.BG.lamTwist C β ν :
            OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g := h1.symm
    _ = ∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        a ν * (Work.BG.lamCF C β g *
          (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g) := by
        apply Finset.sum_congr rfl
        intro ν _
        rw [ha ν, Work.BG.lamTwist_coe, OddOrder.RepresentationTheory.ClassFunction.mul_apply]
    _ = ∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        Work.BG.lamCF C β g *
          (a ν * (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g) := by
        apply Finset.sum_congr rfl
        intro ν _
        ring
    _ = Work.BG.lamCF C β g *
        (∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
        a ν * (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g) :=
        (Finset.mul_sum _ _ _).symm

end Work.BG
