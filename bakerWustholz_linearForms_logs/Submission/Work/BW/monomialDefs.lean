import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Monomials in a tuple of generators of a number field

For a number field `F`, a tuple `β : Fin n → F`, and `d := Module.finrank ℚ F` we consider

* the *unrestricted* monomials `allMono β e = ∏ i, β i ^ (e i)`, for `e : Fin n → ℕ`;
* the *bounded* monomials `bMono β e = ∏ i, β i ^ (e i)`, for `e : Fin n → Fin d`
  (all exponents `< d`).

The point of the bounded ones is that there are only `d ^ n` of them, while (when `β` generates
`F` over `ℚ`) they already span `F`, so one can extract a `ℚ`-basis of `F` consisting of
monomials with exponents `< d`.
-/

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.BW

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- The unrestricted monomial `∏ i, β i ^ (e i)`. -/
noncomputable def allMono (β : Fin n → F) (e : Fin n → ℕ) : F := ∏ i, β i ^ e i

/-- The bounded monomial `∏ i, β i ^ (e i)`, where each exponent is `< Module.finrank ℚ F`. -/
noncomputable def bMono (β : Fin n → F) (e : Fin n → Fin (Module.finrank ℚ F)) : F :=
  ∏ i, β i ^ (e i : ℕ)

@[simp]
lemma allMono_zero (β : Fin n → F) : allMono β 0 = 1 := by
  simp only [allMono, Pi.zero_apply, pow_zero, Finset.prod_const_one]

lemma allMono_add (β : Fin n → F) (e e' : Fin n → ℕ) :
    allMono β (e + e') = allMono β e * allMono β e' := by
  simp only [allMono, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

/-- The monomial of the indicator exponent vector is the corresponding generator. -/
lemma allMono_update_zero (β : Fin n → F) (i : Fin n) :
    allMono β (Function.update 0 i 1) = β i := by
  rw [allMono, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Function.update_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `bMono` is `allMono` of the coerced exponent vector. -/
lemma bMono_eq_allMono (β : Fin n → F) (e : Fin n → Fin (Module.finrank ℚ F)) :
    bMono β e = allMono β (fun i => (e i : ℕ)) := rfl

end Work.BW
