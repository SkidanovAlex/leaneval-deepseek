import Mathlib

/-!
# The linear layer of the model route: projective lines and planes

The mod-2 route to Hugelmeyer's geometric core (`Work.Drive.chainParity`) needs, on the `ℝ × ℝP³`
model side, the two "explicit linear algebra" parity facts named by the project lead:

* two essential loops in `ℝP²` meet an odd number of times;
* three generic planes in `ℝP³` meet an odd number of times.

Both are linear-algebra statements about subspaces once one models `ℝPⁿ` as the projectivisation of
`ℝⁿ⁺¹` (Mathlib's `Projectivization`).  This file fixes the vocabulary: `projLine U` is the set of
points of the projective space represented by a non-zero vector of `U`, so that a projective line in
`ℝP²` is `projLine U` for a `2`-dimensional `U ⊆ ℝ³`, and a projective plane in `ℝP³` is `projLine V`
for a `3`-dimensional `V ⊆ ℝ⁴`.
-/

namespace Work.Drive

/-- The projective line (or plane) of a subspace: the set of points of the projective space
represented by a non-zero vector of `U`.  For `U` of dimension `d` in a space of dimension `d + 1` this
is a projective hyperplane; in particular `projLine U` for a `2`-dimensional `U ⊆ ℝ³` is a projective
line in `ℝP²`, and for a `3`-dimensional `U ⊆ ℝ⁴` a projective plane in `ℝP³`. -/
def projLine {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] (U : Submodule K V) :
    Set (Projectivization K V) :=
  {p | ∃ v : V, ∃ _hv : v ≠ 0, v ∈ U ∧ p = Projectivization.mk K v _hv}


/-- The projective point of a *unit* vector, packaged so that the non-vanishing proof is manufactured
from the norm condition.  This is the map `Sⁿ → ℝPⁿ` whose fibres are the antipodal pairs. -/
noncomputable def projOfUnit {n : ℕ} (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : ‖v‖ = 1) :
    Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  Projectivization.mk ℝ v (by
    intro h
    rw [h] at hv
    simp at hv)

end Work.Drive
