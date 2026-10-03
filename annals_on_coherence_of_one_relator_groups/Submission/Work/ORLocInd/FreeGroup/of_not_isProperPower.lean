import Mathlib
import Submission.Work.ORLocInd.Basic

/-!
# A free generator is not a proper power

`FreeGroup.of a` is a primitive (indeed a free-basis) element, so it cannot be a proper power
`v ^ m` with `m ≥ 2`.  The proof is a one-line argument with the abelianisation: mapping `a` to a
generator of the infinite cyclic group `Multiplicative ℤ` and all other generators to `1` turns an
equation `of a = v ^ m` into `1 = m * c` in `ℤ` with `m ≥ 2`, which is impossible.

This is the analogue, for the `Work.ORLocInd` notion of proper power, of
`Work.OROneRel.not_isProperPower_of` (which uses the `Work.OROneRel` notion).  Note that the
`Work.ORLocInd` definition of `IsProperPower` additionally requires the root `v` to be nontrivial;
the proof does not use this hypothesis.
-/

namespace Work.ORLocInd.FreeGroup

theorem of_not_isProperPower {α : Type*} (a : α) :
    ¬ Work.ORLocInd.IsProperPower (FreeGroup.of a) := by
  classical
  rintro ⟨v, _hv, k, hk, h⟩
  let f : α → Multiplicative ℤ := fun x => if x = a then Multiplicative.ofAdd (1 : ℤ) else 1
  have hk' : FreeGroup.lift f (FreeGroup.of a) = (FreeGroup.lift f v) ^ k := by
    rw [h, map_pow]
  rw [FreeGroup.lift_apply_of] at hk'
  simp only [f, if_pos rfl] at hk'
  have h1 : (1 : ℤ) = (k : ℤ) * (FreeGroup.lift f v).toAdd := by
    have := congrArg Multiplicative.toAdd hk'
    simpa [Int.toAdd_pow] using this
  have h3 : (k : ℤ) = 1 ∨ (k : ℤ) = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h1.symm
  have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast hk
  rcases h3 with h3 | h3 <;> omega

end Work.ORLocInd.FreeGroup
