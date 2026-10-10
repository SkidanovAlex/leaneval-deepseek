import Mathlib
import Submission.Work.MotK.KleinData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The cyclic shift of the Klein (Pfaffian) quadrics, at `kleinP0`

`Work.MotK.kleinP0 a b (fun j => x (i + j)) = Work.MotK.kleinP a b x (3 * i)`:

the first Pfaffian quadric of the coordinate sequence cyclically shifted by `i` is the
`(3 * i)`-th component of `kleinP`.  Equivalently (see `Work.MotK.kleinP_shift`) the shift
`x_j ↦ x_{i + j}` permutes the Pfaffians by `k ↦ k + 3 * i`, which is why `kleinP0` of the
shifted tuple is `kleinP a b x (3 * i)`.

The proof is a finite case check over the five values of `i`: reduce the `Fin 5` index
arithmetic (`Fin.reduceFinMk`, `Fin.reduceAdd`, `Fin.reduceMul`), unpack the two relevant
components of `kleinP` and close the resulting polynomial identity in the atoms
`x 0, …, x 4` with `ring`.
-/

namespace Work.MotV5

theorem kleinP_shift {R : Type*} [CommRing R] (a b : R) (x : Fin 5 → R) (i : Fin 5) :
    Work.MotK.kleinP0 a b (fun j => x (i + j)) = Work.MotK.kleinP a b x ((3 : Fin 5) * i) := by
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceMul,
      Work.MotK.kleinP_zero, Work.MotK.kleinP_one, Work.MotK.kleinP_two,
      Work.MotK.kleinP_three, Work.MotK.kleinP_four,
      Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
      Work.MotK.kleinP4] <;>
    first | refl_ring1 | ring

end Work.MotV5
