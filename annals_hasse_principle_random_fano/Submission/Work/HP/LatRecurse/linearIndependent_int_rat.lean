import Mathlib

namespace Work.HP.LatRecurse

/-- Integer-linear independence of a family of integer vectors is equivalent to
rational-linear independence of the family obtained by casting the coordinates to `ℚ`.

This is the special case `R = ℤ`, `S = ℚ` of Mathlib's
`linearIndependent_algebraMap_comp_iff`, which states that for a commutative ring `R`,
a commutative domain `S` with `R`-algebra structure and faithful `R`-scalar action on `S`,
a family `v : ι → ι' → R` is `R`-linearly independent iff the family obtained by
applying `algebraMap R S` coordinatewise is `S`-linearly independent. -/
theorem linearIndependent_int_rat {R m : ℕ} {f : Fin m → (Fin R → ℤ)} :
    LinearIndependent ℤ f ↔
      LinearIndependent ℚ (fun i => (fun j => ((f i) j : ℚ))) := by
  exact (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ) (v := f)).symm

end Work.HP.LatRecurse
