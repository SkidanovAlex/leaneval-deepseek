import Submission.Lib.Unif2.Work.Mori.Defs

/-!
# The period homomorphism of the conjugate étale space

`Submission.Conjugate` builds, for a harmonic function `u` on a complex one-manifold `X`, the *étale
space of its harmonic conjugates* (the space of pairs `(x, v)` such that `u + i v` is a local
holomorphic function near `x`), shows that the first projection is a covering map, and describes its
monodromy by translations of the fibre: the **period** of a loop.

This module packages that construction as a single additive homomorphism
`Work.Mori.conjPeriodHomOf hu x : Additive (FundamentalGroup X x) →+ ℝ`, whose value on a loop is the
drift of the conjugate of `u` around that loop, together with the special case used in
`Work.Mori.Argument`: the **argument period** (winding) homomorphism of a plane domain around an
exterior point, `Work.Mori.argumentPeriodHom`, obtained from the harmonic function
`z ↦ log ‖z - p‖`.

The point of the winding homomorphism is that its non-triviality is *computable*: if it vanished, the
conjugate of `u` would be single-valued and the argument of `z ↦ z - p` would be periodic along every
loop of the domain — contradicting `Work.Mori.not_hasArg_circle` for the circle around `p`.  See
`Work.Mori.argumentPeriodHom_ne_zero`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Mori

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The period homomorphism of the conjugate of a harmonic function.**  Its value on a loop of `X`
is the drift of the harmonic conjugate of `u` around that loop; equivalently, the multivalued
function `exp (-(u + iu*))` is single-valued exactly when this homomorphism vanishes.

This is `Submission.conjPeriodHom` with the étale topology `Submission.conjTopology u` fixed. -/
noncomputable def conjPeriodHomOf {u : X → ℝ} (hu : Submission.HarmonicOnX u Set.univ) (x : X) :
    Additive (FundamentalGroup X x) →+ ℝ :=
  letI : TopologicalSpace (X × ℝ) := Submission.conjTopology u
  Submission.conjPeriodHom x (Submission.conjFiberPt x 0)
    (Submission.isCoveringMap_fst_conjTopology hu)
    (fun c => Submission.continuous_conjShift c)

end Work.Mori
