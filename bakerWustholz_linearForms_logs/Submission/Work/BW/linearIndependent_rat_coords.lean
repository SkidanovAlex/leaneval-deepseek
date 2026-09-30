import Mathlib
import Submission.Work.BW.sieg2Defs
import Submission.Work.BW.linearIndependent_of_siegCoordF
import Submission.Work.BW.linearIndependent_integralBasis_coords

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℚ`-linear independence in the integral-basis coordinates

Let `v : Fin k → (Fin N → 𝓞 F)` be a family of tuples of algebraic integers of a number field
`F`.  Its *mixed coordinates* `siegCoord (v i) : Fin N → (mixedEmbedding.index F → ℝ)`, i.e.
the `ℝ`-coordinates of the image of `v i` under the mixed embedding, are `ℚ`-linearly
independent by hypothesis.  We show that the same family is `ℚ`-linearly independent when
each entry is written in the `ℚ`-basis `NumberField.integralBasis F` of `F`.

Both coordinate systems are injective `ℚ`-linear maps on the finite dimensional space
`F^N ≅ ℚ^{dN}` (`d = [F : ℚ]`), so independence transfers in both directions.  The two
transfer steps are the imported lemmas:

* `Work.BW.linearIndependent_of_siegCoordF` (mixed coordinates ⟹ the tuple family itself),
* `Work.BW.linearIndependent_integralBasis_coords` (the tuple family ⟹ integral-basis
  coordinates).

The passage from `siegCoord (v i)` to `siegCoordF` applied to the coerced family is
definitional.
-/

namespace Work.BW

theorem linearIndependent_rat_coords {F : Type*} [Field F] [NumberField F] {k N : ℕ}
    (v : Fin k → (Fin N → NumberField.RingOfIntegers F))
    (h : LinearIndependent ℚ (fun i => Work.BW.siegCoord (v i))) :
    LinearIndependent ℚ (fun i => fun (j : Fin N) (l : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) =>
      (NumberField.integralBasis F).repr (((v i j : NumberField.RingOfIntegers F)) : F) l) := by
  exact linearIndependent_integralBasis_coords
    (fun i j => ((v i j : NumberField.RingOfIntegers F) : F))
    (linearIndependent_of_siegCoordF
      (fun i j => ((v i j : NumberField.RingOfIntegers F) : F)) h)

end Work.BW
