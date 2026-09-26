import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.SurgeryInvariance.Abstract
import Submission.Work.SurgeryInvariance.Span.le_sup_of_splits
import Submission.Work.SurgeryInvariance.Span.union_eq_sup
import Submission.Work.SurgeryInvariance.SplitsBy.of_shape
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq
import Submission.Work.SurgeryInvariance.DiscRegion.not_isEssential
import Submission.Work.SurgeryInvariance.WindingSpan.carrier_eq_top
import Submission.Work.SurgeryInvariance.MustBeInessential.windingSpan_eq_bot
import Submission.Work.SurgeryInvariance.DiscRegion.nonempty
import Submission.Work.SurgeryInvariance.DiscRegion.exists_mem_interior
import Submission.Work.SurgeryInvariance.WindingSpan.meridianCurve
import Submission.Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq
import Submission.Work.SurgeryInvariance.Core
import Submission.Work.SurgeryInvariance.Loops
import Submission.Work.SurgeryInvariance.SphereSweep
import Submission.Work.SurgeryInvariance.Sweep.exists_of_single_surgery
import Submission.Work.SurgeryInvariance.Sweep.containsEssentialLoop_of_chain
import Submission.Work.SurgeryInvariance.API
import Submission.Work.SurgeryInvariance.Standard
import Submission.Work.SurgeryInvariance.Bridge

/-!
# `Work.SurgeryInvariance` — invariance of Pardon's essential-piece invariant under `2`-surgeries

This is the entry point of the subproject: importing this module gives the whole area.

Let `P` be a parametrised torus (`Work.CoreTopology.ParamTorus`, e.g. the standard torus
`Work.CoreTopology.standard`) with surface `F = P.carrier`, and let `{S_t}` be a one-parameter
family of spheres in `ℝ³` cutting out the regions `A_t = F ∩ int(S_t)`, transverse to `F` except at
finitely many parameters where a single `2`-surgery takes place.  Pardon's Lemma (`spherefamily`)
says that if `A_0` contains a loop that is essential in `F`, then so does `A_1`.

## The vocabulary

* `Work.SurgeryInvariance.WindingSpan P U ≤ ℚ × ℚ` — the `ℚ`-span of the winding vectors of the
  closed curves of `F` lying in `U ⊆ ℝ³` (the curve-level form of Pardon's
  `im(H₁(F ∩ U; ℚ) → H₁(F; ℚ))`); `Work.SurgeryInvariance.windingOf P γ` is the winding vector of a
  closed curve; `WindingSpan P U = ⊥` holds exactly when `U` contains no essential loop
  (`WindingSpan_eq_bot_iff`, `windingSpan_ne_bot_iff`).
* `Work.SurgeryInvariance.IsOpenInCarrier P U` — `U` is open in the surface `F`.
* `Work.SurgeryInvariance.DiscRegion P` — an embedded closed disc of `F`; with `carrier`,
  `interior`, `boundary` and the certificates `open_interior`, `windingSpan_eq_bot`,
  `windingSpan_interior_eq_bot`, `windingSpan_boundary_eq_bot`.
* `Work.SurgeryInvariance.SplitsBy P A A' D` — no loop of `A` crosses the boundary of `D`.
* `Work.SurgeryInvariance.SurgeryShape P A A'` — the geometric shape of a single `2`-surgery: the
  two regions differ by the interior of an embedded disc, the pieces being disjoint and open.
* `Work.SurgeryInvariance.SurgeryStep P A A'` and
  `Work.SurgeryInvariance.SurgeryStepZero P A A'` — the equivalent loop-level forms.
* `Work.SurgeryInvariance.RegionIsotopic P X Y` — an ambient isotopy of `ℝ³` preserving `F` taking
  `X` to `Y`; `Work.SurgeryInvariance.RegionEquivalent P X Y` — its loop-level content.
* `Work.SurgeryInvariance.Sweep P` — a one-parameter family of regions with finitely many
  `2`-surgeries (isotopies between them, `SurgeryShape` at each exceptional parameter).

## Main results

* `Work.SurgeryInvariance.Sweep.windingSpan_eq` — **the winding span is constant along a sweep**
  (in particular the dichotomy `W t ∈ {⊥, ⊤}` and the `1`-Lipschitz dimension bound are not
  needed);
* `Work.SurgeryInvariance.Sweep.containsEssentialLoop_iff` — the essential-piece invariant is
  constant along the sweep;
* `Work.SurgeryInvariance.Sweep.spherefamily` (**Pardon's Lemma**) and its standard-torus form
  `Work.SurgeryInvariance.Standard.spherefamily`; the same for a family of *spheres* rather than
  regions: `Work.SurgeryInvariance.SphereSweep` with `SphereSweep.spherefamily`,
  `SphereSweep.windingSpan_eq` and `SphereSweep.double_bubble`;
* `Work.SurgeryInvariance.double_bubble_persistence` (**Pardon's `doublebubble`**), in the general
  form `Work.SurgeryInvariance.double_bubble_persistence_of_zero_span` and the sweep form
  `Work.SurgeryInvariance.Sweep.double_bubble`;
* `Work.SurgeryInvariance.Sweep.windingSpan_eq_top` and `Work.SurgeryInvariance.Sweep.dichotomy` —
  along a sweep the dichotomy has to be checked at a single parameter only;
* `Work.SurgeryInvariance.Sweep.hstep` — the local dimension bound of
  `Work.CoreTopology.sphere_family` holds along a sweep, in the sharp form of equality;
* `Work.SurgeryInvariance.windingSpan_eq_of_union_disc` /
  `Work.SurgeryInvariance.containsEssentialLoop_of_union_disc` — the atomic cut-and-paste step;
* `Work.SurgeryInvariance.SweepLoops.spherefamily` — the same theorem for a sweep whose local moves
  are given at the level of loops;
* `Work.SurgeryInvariance.Sweep.exists_of_single_surgery` and
  `Work.SurgeryInvariance.Sweep.containsEssentialLoop_of_chain` — a sweep with one genuine surgery,
  and the finitely-many-surgery form;
* `Work.SurgeryInvariance.exists_windingSpan_not_bot_not_top` — the dichotomy `⊥` / `⊤` fails for the
  concrete invariant (the meridian circle has span `ℚ·(0,1)`), so it cannot be used to obtain the
  invariance;
* `Work.SurgeryInvariance.surgeryShape_of_ball`, `Work.SurgeryInvariance.surgeryStepZero_of_ball` —
  the ball form of the local model of the saddle (`F ∩ b` for an open ball `b`), and
  `Work.SurgeryInvariance.isOpenInCarrier_carrier_inter` (openness of the trace is free);
* `Work.SurgeryInvariance.Sweep.const`, `Work.SurgeryInvariance.exists_sweep_with_essentialLoop` —
  non-vacuity of the hypotheses (there are sweeps whose regions contain essential loops);
* `Work.SurgeryInvariance.MustBeInessential.windingSpan_eq_bot` — Pardon's hypothesis "all curves
  of `S_t ∩ F` are inessential" (proved from `I(F,β)` via `Work.CoreTopology.mustbeinessential`)
  gives `WindingSpan P (F ∩ S_t) = ⊥`;
* `Work.SurgeryInvariance.WindingSpan.carrier_eq_top` — the winding span of the whole torus
  is everything.

See `Submission/Work/SurgeryInvariance/README.md` for a prose account, in particular for the precise
geometric inputs which are *not* available in Mathlib (isotopy extension for the sphere family, and
the local model of the saddle: a small ball around a critical point meets `F` in an embedded disc).
-/
