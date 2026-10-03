import Submission.Work.PlanarSC.PolyTools

/-!
# Dyadic polyominoes

The vocabulary used by the planar simple-connectivity lemmas: a *dyadic polyomino* of level `n` is
the union of the closed dyadic cells `dSq n p` over a finite index set `S`.
-/

open Set

namespace Work.PlanarSC

/-- The union of the closed level-`n` dyadic cells indexed by `S`. -/
def dyadicPolyomino (n : ℕ) (S : Finset (ℤ × ℤ)) : Set ℂ :=
  ⋃ p ∈ S, Commons.Topology.Plane.dSq n p

@[simp]
theorem mem_dyadicPolyomino {n : ℕ} {S : Finset (ℤ × ℤ)} {z : ℂ} :
    z ∈ dyadicPolyomino n S ↔ ∃ p ∈ S, z ∈ Commons.Topology.Plane.dSq n p := by
  simp [dyadicPolyomino]

end Work.PlanarSC
