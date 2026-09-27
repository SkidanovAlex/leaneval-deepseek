import Mathlib
import Submission.Work.KT.Psi.Basic

/-!
# `clsM`: the `K₀`-class of a matrix over an arbitrary finite index type

The definitions of `K₀` (`Submission.Work.KT.Defs`) use `Mat R = Σ n, Matrix (Fin n) (Fin n) R`.
For arguments that reorganise the index set of a matrix (block decompositions, tensor powers,
permutation actions) it is convenient to have the class of a square matrix over an *arbitrary*
finite type, so that no explicit bijection with `Fin` has to be carried around.

`clsM ι M` is `cls` of `M` after the canonical reindexing `ι ≃ Fin (Fintype.card ι)`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A]

/-- The class in `K₀` of a square matrix over an arbitrary finite index type `ι`, reindexed
canonically to `Fin (Fintype.card ι)`. -/
def clsM (ι : Type) [Fintype ι] (M : Matrix ι ι A) : K0 A :=
  clsE M (Fintype.card ι) (Fintype.equivFin ι)

theorem clsM_eq_cls (ι : Type) [Fintype ι] (M : Matrix ι ι A) :
    clsM ι M = cls ⟨Fintype.card ι,
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) M⟩ := rfl

end

end Work.KT.Psi
