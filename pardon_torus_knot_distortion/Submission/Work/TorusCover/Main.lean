import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.Covering
import Submission.Work.TorusCover.Lifting
import Submission.Work.TorusCover.Homotopy
import Submission.Work.TorusCover.Systole
import Submission.Work.TorusCover.Standard
import Submission.Work.TorusCover.Intersections
import Submission.Work.TorusCover.Circles
import Submission.Work.TorusCover.Transport
import Submission.Work.TorusCover.exists_periodShift_eq_sub_of_isLift
import Submission.Work.TorusCover.hasWinding_comp_circleReparam
import Submission.Work.TorusCover.curveLength_meridianCircle_eq
import Submission.Work.TorusCover.exists_torusParam_comp
import Submission.Work.TorusCover.exists_essential_curve_in_ball_radius_one
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

/-!
# The covering-space and winding-number machinery of a parametrised torus

This is the entry point of the `Work.TorusCover` chapter: importing this module gives the whole
area.  A *parametrised torus* is a map `psi : ℝ → ℝ → R3` which is `2π`-periodic in each
variable (i), injective modulo `2π` (ii) and an immersion with a uniform positive lower bound
`c` for its derivative (iii).  Bundled, this is

* `Work.TorusCover.TorusParam` (fields `psi`, `periodic_fst`, `periodic_snd`, `inj_mod`, `c`,
  `c_pos`, `deriv_lower`, `contDiff`),

with the standard torus instance `Work.TorusCover.torusParamModel`
(`psi = Work.Core.torusMap`, `c = 1`) available through
`Work.TorusCover.exists_torusParam_torusMap`.  If `Ψ = Φ.H 1` is an ambient diffeomorphism with
inverse `Ψinv = Φ.Hinv 1` (as in `LeanEval.KnotTheory.PardonDistortion.AmbientIsotopy`), then
`Work.TorusCover.exists_torusParam_comp` pushes a `TorusParam` forward along `Ψinv`, with the
constant divided by a bound on `‖d Ψ‖` over the torus image.

## The covering space

* `Work.TorusCover.psiMap`, `Work.TorusCover.psiMapToRange`: the parametrisation as a map on
  `ℝ × ℝ`, and as a map onto its range;
* `Work.TorusCover.lattice`, `Work.TorusCover.periodShift`: the period lattice `2πℤ²` and its
  elements; `Work.TorusCover.lattice_norm_ge`, `Work.TorusCover.isDiscrete_lattice`,
  `Work.TorusCover.two_pi_le_norm_periodShift` are its metric properties;
* `Work.TorusCover.TorusParam.isCoveringMap_psiMapToRange`: `ℝ² → range psi` is a covering map
  (`Work.TorusCover.isCoveringMap_psiMapToRange` is the same result with the hypotheses given
  explicitly rather than bundled).

## Lifts and the winding vector

* `Work.TorusCover.IsLift`, `Work.TorusCover.IsPeriodicLift`, `Work.TorusCover.HasWinding`;
* `Work.TorusCover.TorusParam.exists_isLift` (path lifting), `Work.TorusCover.isLift_unique`
  (lifts agreeing at one point coincide), `Work.TorusCover.exists_periodShift_eq_sub_of_isLift`
  (any two lifts of the same curve differ by a period shift `periodShift w`);
* `Work.TorusCover.TorusParam.exists_hasWinding`: every continuous closed curve in the range of
  `psi` has a winding vector; `Work.TorusCover.hasWinding_unique`: it is unique;
* `Work.TorusCover.windingVector`, `Work.TorusCover.windingVector_spec`,
  `Work.TorusCover.windingVector_eq`: the winding vector of a closed curve and its
  characterisation, independent of the choice of lift;
* `Work.TorusCover.IsEssential`, `Work.TorusCover.isEssential_iff_windingVector_ne_zero`;
* `Work.TorusCover.hasWinding_zero_of_isLift_periodic`: a curve with a `2π`-periodic lift (a
  constant curve, `Work.TorusCover.hasWinding_zero_of_const`, or a curve lying in a simply
  connected chart) has winding vector `(0,0)`;
* `Work.TorusCover.hasWinding_zero_of_section`: a curve whose image lies in a piece of the torus
  admitting a continuous section of the parametrisation has winding vector `(0,0)`;
* `Work.TorusCover.HomotopicClosed`, `Work.TorusCover.HomotopicClosed.hasWinding_eq`,
  `Work.TorusCover.homotopicClosed_of_same_winding`,
  `Work.TorusCover.homotopicClosed_iff_hasWinding`: two closed curves in the range of `psi` are
  homotopic through closed curves in the range of `psi` **iff** their winding vectors agree.  In
  particular an essential curve is not null-homotopic
  (`Work.TorusCover.not_homotopicClosed_of_isEssential_of_hasWinding_zero`);
* `Work.TorusCover.hasWinding_meridian`, `Work.TorusCover.hasWinding_longitude`: the meridian
  and longitude circles have winding vectors `(0,1)` and `(1,0)`.

## The extrinsic systole

* `Work.TorusCover.exists_dist_lower_bound`: hypothesis (iii) upgrades to a uniform two-point
  bound: for every `ε > 0` there is `δ > 0` with
  `(c - ε) * ‖x - y‖ ≤ ‖psi x - psi y‖` for `‖x - y‖ ≤ δ`;
* `Work.TorusCover.TorusParam.systole_bound` (and the `windingVector`/`IsEssential` variants
  `..._windingVector`, `..._essential`): a closed curve with nonzero winding vector has extrinsic
  length at least `2π c`;
* `Work.TorusCover.TorusParam.systole_bound_integral` (and
  `..._windingVector_integral`): for a `C¹` curve, `2π c ≤ ∫ t in 0..2π, ‖γ' t‖`;
* `Work.TorusCover.TorusParam.two_pi_mul_c_le_totalArcLength`: the same bound directly for the
  total arclength `totalArcLength K` of a smooth `Knot` whose curve lies in the range of `psi`
  and has nonzero winding vector — this is the form used when applying the bound to a knot in
  the isotopy class of the standard `(p,q)` curve;
* `Work.TorusCover.curveLength_le_integral_deriv`: for a `C¹` curve the total variation is at
  most the arclength integral;
* `Work.TorusCover.le_two_mul_radius_of_diam_le`: if every pair of points of `γ` is at distance
  `≥ D`, then `γ` is contained in no closed ball of radius `< D/2`.  (There is *no* bound of the
  form `πc/2` depending only on the immersion constant: `Work.TorusCover.
  exists_essential_curve_in_ball_radius_one` exhibits an essential closed curve on the standard
  torus, whose constant is `1`, contained in a closed ball of radius `1 < π/2`.)

## The standard torus

* `Work.TorusCover.standardTorusCurveLift`, `Work.TorusCover.isLift_standardTorusCurve`,
  `Work.TorusCover.isPeriodicLift_standardTorusCurve`, `Work.TorusCover.hasWinding_standardTorusCurve`,
  `Work.TorusCover.hasWinding_standardTorusCurve_iff`,
  `Work.TorusCover.windingVector_standardTorusCurve`: the standard `(p,q)` curve has lift
  `t ↦ (p t, q t)` and winding vector `(p, q)`; `Work.TorusCover.isEssential_standardTorusCurve`;
* `Work.TorusCover.ncard_standardTorusCurve_meridian`,
  `Work.TorusCover.ncard_standardTorusCurve_longitude`: for `p, q > 0` the standard `(p,q)`
  curve meets each meridian circle in exactly `p` points and each longitude circle in exactly `q`
  points of a fundamental period `[0, 2π)`; equivalently, its algebraic intersection numbers
  with a meridian and a longitude are `p` and `q`.

## Transporting the winding vector

* `Work.TorusCover.hasWinding_comp_left`: changing the ambient map, `γ ↦ Ψ ∘ γ` and
  `psi ↦ Ψ ∘ psi`, keeps the winding vector;
* `Work.TorusCover.hasWinding_comp_circleReparam`: precomposition with an orientation-preserving
  `CircleReparam` keeps the winding vector;
* `Work.TorusCover.hasWinding_comp_standardTorusCurve`: the curve
  `t ↦ Ψ (standardTorusCurve p q (σ.f t))` has winding vector `(p, q)` for the parametrisation
  `(x, y) ↦ Ψ (torusMap x y)` — this is the shape of Pardon's hypothesis
  `Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)`;
* `Work.TorusCover.curveLength_meridianCircle_eq`: the meridian circle has extrinsic length
  exactly `2π`, showing that the systole bound `2π c` is attained (for the standard torus,
  `c = 1`).

## Compatibility with `Work.CoreTopology`

`Work.TorusCover.ParamTorus_exists_liftOf` uses the results above to prove, in the vocabulary of
`Work.CoreTopology` (where `ParamTorus` is a `TorusParam` without the derivative bound and
`ClosedCurve`/`LiftOf` are the bundled curve and lift), that *every* closed curve on a
parametrised torus admits a lift — the path-lifting property for that vocabulary.
-/
