import Mathlib
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.polarParam

/-!
# T4 of the radial-collapse transport: the vocabulary of the fibre sum at `s = 1`

At the collapsed end `s = 1` of the radial collapse
(`Submission/Work/Drive/collapseTransport.lean`), the collapsed count

> `colCount β Q V W 1 = #{(u, y, z) ∈ □ × □ × □ | colPlane β Q 1 u = V y ∧ diskPlane Q u = W z}`

decomposes over the *directions* of the box point `u ∈ □`: with `ζ u = sqDisk (foldBox u)` written in
the polar coordinates of `Submission/Work/Drive/polarParam.lean` as
`ζ u = (1 - 2 σ) · e^{iπt}`, the outer part (`‖ζ u‖ ≥ δ`) of the collapsed plane is the core loop
(`Work.Drive.colPlane_one_of_collar`) and the plane itself is `Q (ζ u)`; hence the two conditions read
exactly as

> `coreLoop Q t = V y`  and  `diamLoop Q t σ = W z`.

`Work.Drive.fibreMeet Q V W` below is the set of the four-tuples `(t, σ, y, z)` satisfying those two
conditions (with `t ∈ [0,1)` — the direction — and `σ ∈ [0,1]` — the signed radius), i.e. the disjoint
union over the directions `t` of the meets of the diameter loop `diamLoop Q t` with the chain `W`,
restricted to the `(t,y)` whose core meet lies on the chain `V`.

The parabolic identity is `Work.Drive.colMeet_one_ncard_eq_fibreMeet` (delegated, statement recorded in
`Submission/Work/Drive/TRANSPORT_COLLAPSE_STATUS.md` §7): with the collar radius `δ` chosen so small
that the disk of radius `δ` misses the cut of `Q` by `W` (which is
`Work.Drive.diskCut_inner_avoid`), the inner part of the collapsed plane contributes nothing and the
reparametrisation above is a bijection.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-- **The fibre meet of the collapsed count at `s = 1`**: the four-tuples `(t, σ, y, z)` of a direction
`t ∈ [0,1)`, a signed radius `σ ∈ [0,1]` and two chain parameters `y, z` of the parameter cube at which
the core loop of `Q` at the direction `t` meets `V` at `y` and the diameter loop at `(t, σ)` meets `W`
at `z`.  This is the target of the reparametrisation of `Work.Drive.colMeet β Q V W 1`. -/
def fibreMeet (Q : ℂ → CappingSpace) (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    Set (ℝ × ℝ × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Set.Ico (0 : ℝ) 1 ∧ p.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧
       p.2.2.1 ∈ Submission.Drive.unitBox 2 ∧ p.2.2.2 ∈ Submission.Drive.unitBox 2 ∧
       coreLoop Q p.1 = V p.2.2.1 ∧ diamLoop Q p.1 p.2.1 = W p.2.2.2}

end

end Work.Drive
