/-
# The condition "`d` vanishes on the row spans of matrices over a subring"

Abstract setting of the lemma `vnClosureGeneration`: `U` is a ring, `d` assigns a real number
to every submodule of `U^n` (`Fin n → U`), and for a subring `R ≤ U` we say that `d` *vanishes*
on `R` if the row span of every matrix over `R` (computed in `U`) has `d`-value zero.
-/
import Mathlib

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.Section3

open Matrix

/-- `RowVanishes d R`: the function `d` vanishes on the row span (inside `U^m`) of every matrix
over the subring `R`. -/
def RowVanishes {U : Type u} [Ring U] (d : (n : ℕ) → Submodule U (Fin n → U) → ℝ)
    (R : Subring U) : Prop :=
  ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
    d m (Submodule.span U (Set.range fun i : Fin n => fun j : Fin m => ((A i j : R) : U))) = 0

end Work.ORHughesFree.Section3
