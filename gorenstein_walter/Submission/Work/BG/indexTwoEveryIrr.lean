import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

theorem indexTwoEveryIrr {H : Type*} [Group H] [Finite H] [Fintype H] (H0 : Subgroup H)
    [H0.Normal] (hind : H0.index = 2) [Invertible (Nat.card H0 : ℂ)]
    [Invertible (Nat.card H : ℂ)]
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter H) :
    ∃ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥H0,
      OddOrder.RepresentationTheory.ClassFunction.inner
        (χ : OddOrder.RepresentationTheory.ClassFunction H ℂ)
        (OddOrder.RepresentationTheory.ClassFunction.induce H0
          (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ)) ≠ 0 := by
  classical
  -- Take an irreducible `ν` of `H0` occurring in the restriction `Res_{H0} χ`.
  obtain ⟨ν, hν⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver (H := H0) χ
  refine ⟨ν, ?_⟩
  -- Frobenius reciprocity turns `⟨χ, Ind ν⟩` into `⟨Res χ, ν⟩ ≠ 0`.
  intro hz
  have hne : (OddOrder.RepresentationTheory.ClassFunction.induce H0
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ)).inner
        (χ : OddOrder.RepresentationTheory.ClassFunction H ℂ) ≠ 0 := by
    rw [OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    exact hν
  exact hne (by rw [OddOrder.RepresentationTheory.ClassFunction.inner_star_comm, hz,
    star_zero])

end Work.BG
