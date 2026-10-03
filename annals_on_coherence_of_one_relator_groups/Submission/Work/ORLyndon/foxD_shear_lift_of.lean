import Mathlib
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero

universe u v

namespace Work.ORLyndon

/-- The Fox derivative, at the letter `x`, of the image of a generator under the `x`-shear
`z ↦ (if z = x then of x * u₀ else of z)` is `1` at `x` and `0` elsewhere, provided `u₀` does not
involve the letter `x`. -/
theorem foxD_shear_lift_of {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (x : α) (u₀ : FreeGroup α) (hx : x ∉ Work.OROneRel.relatorLetters u₀) (q : α) :
    Work.ORLyndon.foxD (K := K) x
      ((FreeGroup.lift (fun z : α => if z = x then FreeGroup.of x * u₀ else FreeGroup.of z))
        (FreeGroup.of q)) = if q = x then 1 else 0 := by
  rw [FreeGroup.lift_apply_of]
  by_cases hq : q = x
  · rw [if_pos hq, Work.ORLyndon.foxD_mul, Work.ORLyndon.foxD_of, if_pos rfl,
      foxD_eq_zero_of_notMem_relatorLetters x u₀ hx, mul_zero, add_zero, if_pos hq]
  · rw [if_neg hq, Work.ORLyndon.foxD_of]

end Work.ORLyndon
