import Submission.Work.CoreTopology.Basic
import Submission.Work.CoreTopology.Winding
import Submission.Work.CoreTopology.Disk
import Submission.Work.CoreTopology.Simplicity
import Submission.Work.CoreTopology.ncard_standardCurve_meridian
import Submission.Work.CoreTopology.ncard_standardCurve_longitude
import Submission.Work.CoreTopology.meridianCurve_boundsDisk
import Submission.Work.CoreTopology.longitudeCurve_boundsDisk
import Submission.Work.CoreTopology.encard_meridian_inter_standardCurve
import Submission.Work.CoreTopology.encard_longitude_inter_standardCurve
import Submission.Work.CoreTopology.essential_diameter_ge_two
import Submission.Work.CoreTopology.torusMap_winding_diameter
import Submission.Work.CoreTopology.positive_scale
import Submission.Work.CoreTopology.homDim_const
import Submission.Work.CoreTopology.sphere_family
import Submission.Work.CoreTopology.PieceData
import Submission.Work.CoreTopology.DoubleBubble
import Submission.Work.CoreTopology.MustBeInessential
import Submission.Work.CoreTopology.EssentialLoop
import Submission.Work.CoreTopology.IntersectionNumber
import Submission.Work.CoreTopology.IntersectionNumberStandard
import Submission.Work.CoreTopology.circle_lift_eq_of_extends_disk
import Submission.Work.CoreTopology.compressing_winding_dichotomy
import Submission.Work.CoreTopology.min_le_encard_inter_standardCurve
import Submission.Work.CoreTopology.MustBeInessentialStandard
import Submission.Work.CoreTopology.Transport
import Submission.Work.CoreTopology.pardonsI_mapHomeomorph
import Submission.Work.CoreTopology.IntersectionNumberDiffeomorphic

/-!
# Pardon's topological core for the torus-knot distortion bound

This directory formalises the *purely topological* part of John Pardon's proof of the lower
bound `δ(T_{p,q}) ≥ min(p,q)/160` for the distortion of torus knots (Theorem 1.3 of "On the
distortion of knots on embedded surfaces", specialised to the standard torus).

## The vocabulary

* `Work.CoreTopology.ParamTorus` — a parametrised embedded torus `psi : ℝ → ℝ → ℝ³`, `2π`-periodic
  in each variable and injective modulo `2π`; `P.carrier` is the surface `F`.  `Work.CoreTopology.standard`
  is the torus of revolution of major radius `2` and minor radius `1` (whose parametrisation is
  `Work.Core.torusMap`).
* `Work.CoreTopology.ClosedCurve P` — a continuous `2π`-periodic curve lying in `F`;
  `ParamTorus.meridianLoop`, `ParamTorus.longitudeLoop`, `Work.CoreTopology.meridianCurve`,
  `Work.CoreTopology.longitudeCurve` for the two families of circles.
* `Work.CoreTopology.LiftOf` — a continuous lift `(Θ, Φ) : ℝ → ℝ²` of a closed curve to the
  parameter plane; `LiftOf.winding : ℤ × ℤ` — its winding vector, independent of the lift
  (`LiftOf.winding_eq`).  `Work.CoreTopology.IsEssential P γ` says that the winding vector is
  nonzero, i.e. that the loop is *not* null-homotopic in `F`.
* `Work.CoreTopology.IsSimple P γ` — `γ` is injective on a fundamental period (a simple loop).
* `Work.CoreTopology.IsBoundingDisk`, `Work.CoreTopology.BoundsDiskInComplement` — the curve
  bounds an embedded disc in `ℝ³` whose interior is disjoint from `F` (Pardon's set `U`).
* `Work.CoreTopology.pardonsI P β` — Pardon's invariant `I(F, β)`: the infimum of `|α ∩ β|`
  over simple closed curves `α` of `F` that bound a disc in the complement of `F`.
* `Work.CoreTopology.Homotopic` — homotopy of closed curves inside `F`.
* `Work.CoreTopology.HomPieceData` — the homological invariant `im(H₁(F ∩ U;ℚ) → H₁(F;ℚ))`
  attached to a region `U`, with `HomPieceData.HasEssentialLoop` and `HomPieceData.Dichotomy`.
* `Work.CoreTopology.ContainsEssentialLoop` — a region of `ℝ³` contains a loop of `F` with
  nonzero winding vector.

## Main results

* **Deliverable 1 — the invariant for the standard torus.**
  `Work.CoreTopology.pardonsI_standard` : for `p, q > 0` coprime,
  `pardonsI standard (standardCurve p q) = min p q`.
  Ingredients: `meridianCurve_boundsDisk`, `longitudeCurve_boundsDisk` (the two circles bound
  discs in the complement of the torus), `encard_meridian_inter_standardCurve`,
  `encard_longitude_inter_standardCurve` (the `(p,q)`-curve meets the meridian in `p` and the
  longitude in `q` points), `compressing_winding_dichotomy` (every compressing loop is homotopic
  to a multiple of the meridian or of the longitude), and
  `min_le_encard_inter_standardCurve` (the induced intersection-number lower bound).
  For a torus that is the image of the standard one under a homeomorphism `ψ` of `ℝ³`,
  `Work.CoreTopology.pardonsI_mapHomeomorph` (invariance of `I` under `ψ`) and
  `Work.CoreTopology.pardonsI_standard_mapHomeomorph` give the same computation.

* **Deliverable 2 — Pardon's `mustbeinessential`.**
  `Work.CoreTopology.mustbeinessential` : if the sphere `S` meets `β` in fewer than `I(F,β)`
  points, then every closed curve of `F` contained in `S` is inessential; geometric form
  `Work.CoreTopology.mustbeinessential_geometric`, together with the unconditional standard-torus
  form `Work.CoreTopology.not_containsCompressingLoop_of_encard_lt`.

* **Deliverable 3 — Pardon's `doublebubble` and `spherefamily`.**
  `Work.CoreTopology.homDim_const` (the numerical core: an `ℕ`-valued function taking only the
  values `0` and `D > 1` and changing by at most `1` is constant),
  `Work.CoreTopology.sphere_family` (the abstract sphere-family lemma over `Submodule ℚ A`),
  `Work.CoreTopology.double_bubble` and its geometric form
  `Work.CoreTopology.double_bubble_geometric`.

* **Deliverable 4 — positive scale.**
  `Work.CoreTopology.essential_diameter_ge_two` (an essential closed curve of the standard torus
  has diameter at least `2`), `Work.CoreTopology.positive_scale` (a ball containing an essential
  loop has radius at least `1`), `Work.CoreTopology.positive_scale_set` (the set of such radii is
  bounded below by the positive constant `1`), `Work.CoreTopology.essentialBallRadii`,
  `Work.CoreTopology.not_containsEssentialLoop_closedBall_of_lt_one`.

* **Supporting results**: `Work.CoreTopology.circle_lift_eq_of_extends_disk` (the winding number
  of a null-homotopic loop in the circle vanishes), `Work.CoreTopology.torusMap_winding_diameter`,
  `Work.CoreTopology.encard_*`, `Work.CoreTopology.meridianCurve_simple`,
  `Work.CoreTopology.longitudeCurve_simple`.

See `Submission/Work/CoreTopology/README.md` for a prose account.
-/

namespace Work.CoreTopology

end Work.CoreTopology
