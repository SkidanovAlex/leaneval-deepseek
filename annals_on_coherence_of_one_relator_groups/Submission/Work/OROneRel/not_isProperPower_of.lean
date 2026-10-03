import Mathlib
import Submission.Work.OROneRel.Basic

universe u

namespace Work.OROneRel

/-- A free generator `of a` is never a proper power: mapping `a` to a generator of the infinite
cyclic group `Multiplicative ℤ` and every other generator to `1` turns `of a = u ^ k` into
`1 = k * (φ u).toAdd` in `ℤ`, which is impossible for `k ≥ 2`. -/
theorem not_isProperPower_of {α : Type u} (a : α) :
    ¬ Work.OROneRel.IsProperPower (FreeGroup.of a) := by
  classical
  rintro ⟨u, k, hk, h⟩
  let f : α → Multiplicative ℤ := fun x => if x = a then Multiplicative.ofAdd (1 : ℤ) else 1
  have hk' : FreeGroup.lift f (FreeGroup.of a) = (FreeGroup.lift f u) ^ k := by
    rw [h, map_pow]
  rw [FreeGroup.lift_apply_of] at hk'
  simp only [f, if_pos rfl] at hk'
  have h1 : (1 : ℤ) = (k : ℤ) * (FreeGroup.lift f u).toAdd := by
    have := congrArg Multiplicative.toAdd hk'
    simpa [Int.toAdd_pow] using this
  have h3 : (k : ℤ) = 1 ∨ (k : ℤ) = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h1.symm
  have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast hk
  rcases h3 with h3 | h3 <;> omega

end Work.OROneRel
