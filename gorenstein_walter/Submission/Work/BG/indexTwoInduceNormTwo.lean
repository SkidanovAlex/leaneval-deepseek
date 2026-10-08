import Mathlib
import Submission.Work.BG.CharBridge
import Submission.Work.BG.indexTwoMackey

namespace Work.BG

open OddOrder.RepresentationTheory

set_option linter.style.haveILetI false in

theorem indexTwoInduceNormTwo {H : Type*} [Group H] [Finite H] [Fintype H] (H0 : Subgroup H)
    [H0.Normal] (hind : H0.index = 2) (s : H) (hs : s ∉ H0)
    [Invertible (Nat.card H0 : ℂ)] [Invertible (Nat.card H : ℂ)]
    (ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥H0)
    (hν : OddOrder.RepresentationTheory.ClassFunction.conjBy s
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ) =
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ)) :
    OddOrder.RepresentationTheory.ClassFunction.inner
      (OddOrder.RepresentationTheory.ClassFunction.induce H0
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ))
      (OddOrder.RepresentationTheory.ClassFunction.induce H0
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥H0 ℂ)) = 2 := by
  -- `H₀` is fintype as a subtype of the fintype `H` (only `Finite` is derived automatically,
  -- since membership in `H₀` need not be decidable).
  haveI : Fintype ↥H0 := Fintype.ofFinite _
  -- Frobenius reciprocity: `⟨Ind ν, Ind ν⟩_H = ⟨ν, Res (Ind ν)⟩_{H₀}`.
  rw [ClassFunction.inner_induce_eq_inner_restrict H0]
  -- The index-two Mackey formula: `Res (Ind ν) = ν + ν^s`.
  rw [Work.BG.indexTwoMackey H0 hind s hs (ν : ClassFunction ↥H0 ℂ)]
  -- Bilinearity, invariance `ν^s = ν`, and orthonormality `⟨ν, ν⟩ = 1`.
  rw [ClassFunction.inner_add_right, hν, irreducibleCharacter_inner_eq_ite ν ν]
  norm_num

end Work.BG
