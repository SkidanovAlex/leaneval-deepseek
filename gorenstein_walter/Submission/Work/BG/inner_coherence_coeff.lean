import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.lemma17_iii_aux
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_lemma17T

namespace Work.BG

theorem inner_coherence_coeff {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
      OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hf : Work.GW2.C16.IsCoherent C f)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    {ν η : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ}
    (hν : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν)
    (hη : OddOrder.RepresentationTheory.IsIrreducibleCharacter η)
    (hlam : Work.BG.LamEquiv C ν η) :
    OddOrder.RepresentationTheory.ClassFunction.inner χ (f ν - f η) =
      OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ) (ν - η) := by
  -- GoodOn (clause (iii) of Theorem 2.3) at the pair `(ν, η)` of the key `Λν ∪ (Λν)^s`:
  -- `ν` and `η` are both on that key (`ν` by reflexivity, `η` by `hlam`), and they are
  -- irreducible, so `ν̃ - η̃ = (ν - η)^G`, i.e. `f ν - f η = ind C (ν - η)`.
  have hgood := (hf.1 ν hν) ν (Or.inl (s02c_LamEquiv_refl C ν)) η (Or.inl hlam) hν hη
  have hind : ind C (ν - η) = f ν - f η := hgood.2.2.2.1 hlam
  rw [← hind]
  -- Frobenius reciprocity in the orientation `(χ, θ^G)_G = (χ|_{H₀}, θ)_{H₀}`.
  exact inner_induce_eq_inner_restrict_right χ (ν - η)

end Work.BG
