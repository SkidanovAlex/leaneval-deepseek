import Mathlib
import Submission.Work.Mostow.gapA.axisNormDefs
import Submission.Work.Mostow.gapA.normSub_orthonormalBasis
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.geodEquiv
import Submission.Work.Mostow.fermi_measurePreserving
import Submission.Work.Mostow.gapA.tubeDefs

/-!
# Fermi coordinates for the geodesic `geodSet a b`, and the standard chart

The target `Work.Mostow.gapA.volH3Slab` computes the volume of a Fermi slab
`{s ≤ sig a b u < s + L, distGeod a b u ≤ R}` of `ℍ³`.  The plan is to transport the standard
Fermi chart `fermi 1 2` (about the standard geodesic `stdTG 1 2`, whose endpoints on the sphere
are `stdA` and `stdB = -stdA`) to the geodesic joining `a` and `b` by an explicit isometry.

Given an orthonormal (`mink`-orthonormal, positive definite) basis `B : AxisBasis a b` of the
normal plane `NormSub a b`, the point with Fermi coordinates `(v, w)` (`v : E 1` the axis
coordinate, `w : E 2` the normal vector, `‖w‖` = distance to the geodesic) has hyperboloid
coordinates

  `axisPt_slabDefs a b B v w = cosh ‖w‖ • axis (arsinh (v 0)) + sinhc ‖w‖ • (w 0 • E1 + w 1 • E2)`

where `gcAxis a b s` is the axis point of the Minkowski parameter `s`; its chart representation
is `chartPt a b B v w`.  The composite `chartMap a b B = chartPt a b B ∘ fermiInv 1 2` is the
chart-level isometry from the standard Fermi chart to this one.

Everything in this file is definitions; the lemmas live in `volH3Slab.lean`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The standard first boundary point (the first basis vector of `E 3`, on `Sph 3`). -/
def stdA : E 3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The antipodal standard boundary point. -/
def stdB : E 3 := -stdA

/-- The standard first normal direction (`E1` of `AxisBasis stdA stdB`). -/
def stdE1 : Fin 3 ⊕ Fin 1 → ℝ := Pi.single (Sum.inl 1) 1

/-- The standard second normal direction (`E2` of `AxisBasis stdA stdB`). -/
def stdE2 : Fin 3 ⊕ Fin 1 → ℝ := Pi.single (Sum.inl 2) 1

/-- The Minkowski point with Fermi coordinates `(v,w)` around the geodesic `geodSet a b`,
using the normal basis `B`. -/
def axisPt_slabDefs (a b : E 3) (B : AxisBasis a b) (v : E 1) (w : E 2) : Fin 3 ⊕ Fin 1 → ℝ :=
  Real.cosh ‖w‖ • gcAxis a b (Real.arsinh (v 0)) +
    Submission.Mostow.sinhc ‖w‖ • (w 0 • B.E1 + w 1 • B.E2)

/-- The chart representation of `axisPt_slabDefs`. -/
def chartPt (a b : E 3) (B : AxisBasis a b) (v : E 1) (w : E 2) : E 3 :=
  WithLp.toLp 2 (fun i : Fin 3 => axisPt_slabDefs a b B v w (Sum.inl i))

/-- The chart-level isometry from the standard Fermi chart to the `(a,b)` Fermi chart. -/
def chartMap (a b : E 3) (B : AxisBasis a b) (u : E 3) : E 3 :=
  chartPt a b B (fermiInv 1 2 u).1 (fermiInv 1 2 u).2

end

end Work.Mostow.gapA
