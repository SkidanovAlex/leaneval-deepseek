import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- A field `L` carrying an `F`-algebra structure with `F` of characteristic `5` itself has
characteristic `5`: the structure map `algebraMap F L` is injective (a ring homomorphism out of a
field into a nontrivial ring), and characteristic is transported along injective ring
homomorphisms. -/
lemma charP_algebra_of_charP {F L : Type*} [Field F] [Field L] [Algebra F L] [CharP F 5] :
    CharP L 5 :=
  charP_of_injective_algebraMap (RingHom.injective (algebraMap F L)) 5

/-- In a field of characteristic `5`, the five elements `w, w+1, w+2, w+3, w+4` are pairwise
distinct.  Indeed `w + a = w + b` forces `((i : ℕ) : L) = ((j : ℕ) : L)`, and on the interval
`{0,1,2,3,4}` the natural-number cast into a ring of characteristic `5` is injective. -/
theorem w_add_injective {F L : Type*} [Field F] [Field L] [Algebra F L] [CharP F 5]
    (w : L) : Function.Injective (fun i : Fin 5 => w + ((i:ℕ):L)) := by
  have hchar : CharP L 5 := charP_algebra_of_charP (F := F)
  intro i j h
  apply Fin.ext
  have h' : ((i : ℕ) : L) = ((j : ℕ) : L) := add_left_cancel h
  exact CharP.natCast_injOn_Iio L 5 i.isLt j.isLt h'

end Work.MotV5
