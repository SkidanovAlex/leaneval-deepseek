import Mathlib
import Submission.Work.BSW.Char.Setup

open OddOrder.RepresentationTheory

namespace Work.BSW.Char

/-- The character sum `∑_χ χ(t)² χ(x)/χ(1)` is unchanged when `x` is replaced by `x⁻¹`, for an
involution `t`.

Route: the involution `χ ↦ χ̄`
(`OddOrder.RepresentationTheory.IrreducibleCharacter.conjPerm`, with `conjPerm_apply_coe` and
`ClassFunction.conj_apply`) permutes the irreducible characters, so reindexing by it gives
`∑_χ χ(t)² χ(x)/χ(1) = ∑_χ star(χ t)² · star(χ x) / star(χ 1)` (`Equiv.sum_comp`).  Now
`star (χ t) = χ t` because `star (χ t) = χ t⁻¹ = χ t` (`irreducibleCharacter_apply_inv` plus
`t⁻¹ = t` from `ht`), `star (χ 1) = χ 1⁻¹ = χ 1`, and `star (χ x) = χ x⁻¹`
(`irreducibleCharacter_apply_inv`). -/
theorem sum_char_div_eq_sum_char_inv {G : Type} [Group G] [Finite G] {t x : G} (ht : t * t = 1) :
    (∑ χ : OddOrder.RepresentationTheory.IrreducibleCharacter G,
        (((χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) t) ^ 2 *
          (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) x) /
        (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1) =
      ∑ χ : OddOrder.RepresentationTheory.IrreducibleCharacter G,
        (((χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) t) ^ 2 *
          (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) x⁻¹) /
        (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 := by
  -- `t` is an involution, so `t⁻¹ = t`.
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  -- Value of the conjugate character at `t` is `χ t` itself.
  have hconjT : ∀ χ : IrreducibleCharacter G,
      ((IrreducibleCharacter.conjPerm G χ : IrreducibleCharacter G) : ClassFunction G ℂ) t
        = (χ : ClassFunction G ℂ) t := by
    intro χ
    rw [IrreducibleCharacter.conjPerm_apply_coe, ClassFunction.conj_apply,
      ← irreducibleCharacter_apply_inv χ t, htinv]
  -- Value of the conjugate character at `x` is `χ x⁻¹`.
  have hconjX : ∀ χ : IrreducibleCharacter G,
      ((IrreducibleCharacter.conjPerm G χ : IrreducibleCharacter G) : ClassFunction G ℂ) x
        = (χ : ClassFunction G ℂ) x⁻¹ := by
    intro χ
    rw [IrreducibleCharacter.conjPerm_apply_coe, ClassFunction.conj_apply,
      ← irreducibleCharacter_apply_inv χ x]
  -- … and at `1` it is `χ 1`.
  have hconjOne : ∀ χ : IrreducibleCharacter G,
      ((IrreducibleCharacter.conjPerm G χ : IrreducibleCharacter G) : ClassFunction G ℂ) 1
        = (χ : ClassFunction G ℂ) 1 := by
    intro χ
    rw [IrreducibleCharacter.conjPerm_apply_coe, ClassFunction.conj_apply,
      ← irreducibleCharacter_apply_inv χ 1, inv_one]
  -- Reindex the left-hand sum along the conjugation involution on irreducible characters.
  rw [← Equiv.sum_comp (IrreducibleCharacter.conjPerm G)
        (fun χ : IrreducibleCharacter G =>
          (((χ : ClassFunction G ℂ) t) ^ 2 * (χ : ClassFunction G ℂ) x) /
          (χ : ClassFunction G ℂ) 1)]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  rw [hconjT χ, hconjX χ, hconjOne χ]

end Work.BSW.Char
