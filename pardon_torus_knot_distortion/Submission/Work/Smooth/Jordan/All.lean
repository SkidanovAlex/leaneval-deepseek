import Submission.Work.Smooth.Jordan.Defs
import Submission.Work.Smooth.Jordan.Index
import Submission.Work.Smooth.Jordan.wind_mem_int
import Submission.Work.Smooth.Jordan.Circle
import Submission.Work.Smooth.Jordan.unitCircle_isSimple
import Submission.Work.Smooth.Jordan.unitCircle_wind_inside
import Submission.Work.Smooth.Jordan.unitCircle_wind_outside
import Submission.Work.Smooth.Jordan.Separation
import Submission.Work.Smooth.Jordan.plane_separation_preconnected_subset
import Submission.Work.Smooth.Jordan.plane_separation_unbounded
import Submission.Work.Smooth.Jordan.plane_separation_component_U
import Submission.Work.Smooth.Jordan.plane_separation_component_V
import Submission.Work.Smooth.Jordan.plane_separation_eq
import Submission.Work.Smooth.Jordan.plane_schoenflies_openDisc_eq
import Submission.Work.Smooth.Jordan.plane_schoenflies_convex
import Submission.Work.Smooth.Jordan.JordanIndex
import Submission.Work.Smooth.Jordan.ind_local
import Submission.Work.Smooth.Jordan.ind_vanishes_at_infinity
import Submission.Work.Smooth.Jordan.ind_abs_le_one
import Submission.Work.Smooth.Jordan.ind_eq_zero_iff
import Submission.Work.Smooth.Jordan.ind_ne_zero_iff
import Submission.Work.Smooth.Jordan.ind_const_on_preconnected
import Submission.Work.Smooth.Jordan.unitCircle_jordanSchoenflies
import Submission.Work.Smooth.Jordan.Sphere
import Submission.Work.Smooth.Jordan.sphere_schoenflies_map_homeomorph
import Submission.Work.Smooth.Jordan.schoenfliesOnInput_of_homeomorph
import Submission.Work.Smooth.Jordan.Family
import Submission.Work.Smooth.Jordan.family_disc_eq
import Submission.Work.Smooth.Jordan.family_insideOpen_trans
import Submission.Work.Smooth.Jordan.family_insideOpen_imp_inside
import Submission.Work.Smooth.Jordan.family_insideOpen_strictOrder
import Submission.Work.Smooth.Jordan.sphereSchoenflies_openDisc_compl
import Submission.Work.Smooth.Jordan.familyDiscs_of_schoenfliesData
import Submission.Work.Smooth.Jordan.familyDiscs_of_jordanSchoenfliesSphere
import Submission.Work.Smooth.Jordan.Application

/-!
# `Work.Smooth.Jordan` — the smooth Jordan–Schoenflies chapter

Entry point of the chapter: `import Submission.Work.Smooth.Jordan.All`.  See
`Submission/Work/Smooth/Jordan/README.md` for the full account of what is defined, what is proved,
and what is the remaining classical input.

## Layout

* `Defs.lean` — the vocabulary: `Disc` (`𝔻`), `circlePoint`, `PlaneCurve`, `SmoothPlaneCurve`,
  `PlaneCurve.IsSimple`, `PlaneCurve.trace`, `IsSimpleClosedCurveOn`, `IsEmbeddedCircle`,
  `IsSpanningDisc`, `IsSpanningDiscOn`, `openDisc`;
* `Index.lean` — the winding integral `wind` and the index `ind`;
* `wind_mem_int.lean` — the index is an integer (integrality of the winding number);
* `Circle.lean`, `unitCircle_*.lean` — the standard circle: simple, its winding integrals inside
  and outside, and the fact that it satisfies the whole plane input;
* `Separation.lean` — `PlaneSeparation`, `PlaneSchoenflies`, the classical inputs `JordanInput`,
  `SchoenfliesInput`, `ClassicalInput`;
* `plane_separation_*.lean`, `plane_schoenflies_*.lean` — the plane separation API and the
  convexity form of Schoenflies;
* `JordanIndex.lean` — `ind_eq_wind`, the full classical input `PlaneJordanSchoenflies`, and its
  derivations `ind_eq_one_or_neg_one`, `ind_ne_zero_V`; `ind_*.lean` — local constancy, vanishing
  at infinity, the identification of the two sides with the index level sets and `|ind| ≤ 1`;
* `Sphere.lean` — `SphereSchoenflies` (two complementary discs on a surface `A ⊆ ℝ³`),
  `SchoenfliesOnInput A`, `RoundSphere`; `sphere_schoenflies_map_homeomorph.lean`,
  `schoenfliesOnInput_of_homeomorph.lean` — transport along homeomorphisms, hence Schoenflies on
  every surface homeomorphic to `S²` (in particular the box boundary) from Jordan–Schoenflies on
  the round sphere;
* `Family.lean` — `FamilyDiscs` (a finite family of disjoint simple closed curves with nested
  spanning discs), the containment relation `FamilyDiscs.InsideOpen` / `FamilyDiscs.Inside`, and
  **`FamilyDiscs.exists_innermost`** / `FamilyDiscs.exists_innermost_curve`; the strict order
  properties are in `family_insideOpen_trans.lean` and `FamilyDiscs.not_insideOpen_self`;
  `familyDiscs_of_schoenfliesData.lean` converts the classical `SchoenfliesData` of the sibling
  chapter into `FamilyDiscs`;
* `Application.lean` — item 5: `InnermostDiscInput` and `CleansInSphere` for the tori
  `ParamTorus.mapHomeomorph ψ` of the challenge and the boundary of Pardon's box, from the classical
  input `Work.Topology.Classical.ClassicalTopology`.
-/
