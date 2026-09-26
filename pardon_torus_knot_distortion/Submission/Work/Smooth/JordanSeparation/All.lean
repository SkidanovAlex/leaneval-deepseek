import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.Index
import Submission.Work.Smooth.JordanSeparation.exists_transverse_lipschitz_field
import Submission.Work.Smooth.JordanSeparation.offset_injective
import Submission.Work.Smooth.JordanSeparation.atMostTwo_connectedComponentIn_of_offset
import Submission.Work.Smooth.JordanSeparation.AtMostTwo
import Submission.Work.Smooth.JordanSeparation.exists_normal_offset_notMem_trace
import Submission.Work.Smooth.JordanSeparation.wind_normal_offset_sub
import Submission.Work.Smooth.JordanSeparation.tendsto_winding_jump_integral
import Submission.Work.Smooth.JordanSeparation.Jump
import Submission.Work.Smooth.JordanSeparation.nonempty_planeSeparation
import Submission.Work.Smooth.JordanSeparation.Separation
import Submission.Work.Smooth.JordanSeparation.Main
import Submission.Work.Smooth.JordanSeparation.Corollaries
import Submission.Work.Smooth.JordanSeparation.frontier_eq_trace
import Submission.Work.Smooth.JordanSeparation.Frontier
import Submission.Work.Smooth.JordanSeparation.WeakDefs
import Submission.Work.Smooth.JordanSeparation.DenomWeak
import Submission.Work.Smooth.JordanSeparation.ModelWeak
import Submission.Work.Smooth.JordanSeparation.JumpIntegralWeak
import Submission.Work.Smooth.JordanSeparation.JumpOnRegular
import Submission.Work.Smooth.JordanSeparation.SimpleCurves
import Submission.Work.Smooth.JordanSeparation.LocalFrame
import Submission.Work.Smooth.JordanSeparation.LocalSides
import Submission.Work.Smooth.JordanSeparation.FrontierComponent
import Submission.Work.Smooth.JordanSeparation.AtMostTwoGeneral
import Submission.Work.Smooth.JordanSeparation.MainGeneral
import Submission.Work.Smooth.JordanSeparation.NoSeparation
import Submission.Work.Smooth.JordanSeparation.Unconditional
import Submission.Work.Smooth.JordanSeparation.ind_eq_zero_of_avoiding_extension
import Submission.Work.Smooth.JordanSeparation.SchoenfliesReduction
import Submission.Work.Smooth.JordanSeparation.offset_notMem_trace
import Submission.Work.Smooth.JordanSeparation.alexander_cone_extension
import Submission.Work.Smooth.JordanSeparation.curve_arg_continuous
import Submission.Work.Smooth.JordanSeparation.planeSchoenflies_of_star_shaped
import Submission.Work.Smooth.JordanSeparation.innerCurve_isSimple
import Submission.Work.Smooth.JordanSeparation.Transfer
import Submission.Work.Smooth.JordanSeparation.CollarTransfer
import Submission.Work.Smooth.JordanSeparation.CircleBase
import Submission.Work.Smooth.JordanSeparation.LocalTangency
import Submission.Work.Smooth.JordanSeparation.BumpCylinder
import Submission.Work.Smooth.JordanSeparation.BumpStep
import Submission.Work.Smooth.JordanSeparation.collar_side
import Submission.Work.Smooth.JordanSeparation.ChordWindow
import Submission.Work.Smooth.JordanSeparation.exists_homeomorph_of_compatible_chain
import Submission.Work.Smooth.JordanSeparation.discExtension_of_cylinder_chain
import Submission.Work.Smooth.JordanSeparation.CapCut
import Submission.Work.Smooth.JordanSeparation.RemainingGap

/-!
# `Work.Smooth.JordanSeparation` — the Jordan separation theorem for a simple closed plane curve

Import `Submission.Work.Smooth.JordanSeparation.All` for everything (namespace
`Work.Smooth.JordanSeparation`).  See `README.md` in this directory.

## Main results

The Jordan separation theorem is **proved** for every `C¹` `2π`-periodic plane curve which is
injective on one period — cusps allowed, no immersion hypothesis:

* `jordanSeparation_of_isSimple` — `Nonempty (PlaneSeparation c.toPlaneCurve)` for a
  `SmoothPlaneCurve` (`Unconditional.lean`);
* `planeSeparation_of_contDiff_of_isSimple` — the same for a bare `PlaneCurve` of class `C¹`;
* `jordanInput_of_contDiff` — the same in the shape of the sibling chapter's
  `Work.Smooth.Jordan.JordanInput`;
* `nonempty_planeJordanSeparation_of_isSimple` — the separation together with the index values
  `ind c x = 0` on the unbounded side and `|ind c x| = 1` on the bounded side;
* `smoothSimpleInput`, `contDiffSimpleInput` — the class of curves covered, as a `Prop`.

The only classical input of the planar picture that is not proved here is the Jordan–Schoenflies
theorem (the spanning embedded disc); `planeJordanSchoenflies_of_planeSchoenflies` reduces the
sibling chapter's full classical input to exactly that.

## Layout

* `Defs.lean` — the vocabulary: `detV`, `unitTangent`, `normalField`, `IsTransverseUnitField`,
  `IsLipschitzField`, `offset`, `annulus`, `posPart`, `negPart`, `zeroPart`;
* `Index.lean` — `ind_eq_zero_of_unbounded` (the index vanishes on an unbounded preconnected set);
* `exists_transverse_lipschitz_field.lean` — a Lipschitz unit field uniformly transverse to an
  immersed closed curve exists;
* `offset_injective.lean` — its offset map is injective on a strip modulo the period;
* `atMostTwo_connectedComponentIn_of_offset.lean` — **at most two components** from such an offset
  neighbourhood;
* `AtMostTwo.lean` — `atMostTwo_connectedComponentIn` for a `C¹` immersed simple closed curve;
* `exists_normal_offset_notMem_trace.lean` — the normal offsets miss the curve;
* `wind_normal_offset_sub.lean` — the algebra of the difference of the two winding integrals;
* `tendsto_winding_jump_integral.lean` — the asymptotics of that difference;
* `Jump.lean` — **the index jumps by `1`** across a regular point of the curve;
* `nonempty_planeSeparation.lean` — the two component counts give `PlaneSeparation`;
* `Separation.lean` — Jordan separation for an immersion, and the values of the index on the sides;
* `Main.lean` — `PlaneJordanSeparation`, `jordanInput_of_smooth`, `smoothImmersionInput`;
* `Corollaries.lean` — the sides are the index level sets, `ind ∈ {0, ±1}` and `|ind| ≤ 1` off the
  trace, and the sides are independent of the choice of `PlaneSeparation`;
* `frontier_eq_trace.lean` — the parameter shift `shiftCurve` of a curve, the invariance of
  `wind`/`ind` under it, `ind_jump_at`, and `PlaneCurve.IsSimple.eq_mod_period`;
* `Frontier.lean` — the frontiers and closures of the two sides (immersion);
* `WeakDefs.lean`, `DenomWeak.lean`, `ModelWeak.lean`, `JumpIntegralWeak.lean`,
  `JumpOnRegular.lean` — the index jump with `deriv c.γ 0 ≠ 0` in place of `c.IsImmersion`;
* `SimpleCurves.lean` — for a `C¹` simple closed curve: the existence of a regular parameter,
  **at least two components**, the index values on the sides;
* `LocalFrame.lean`, `LocalSides.lean` — the local frame at a point of the curve and **`local_sides`**:
  the two local sides at *any* point of a `C¹` simple closed curve;
* `FrontierComponent.lean` — `frontier_connectedComponentIn_eq` and **`frontier_component_continuum`**:
  the frontier of a complementary domain of a continuum is a non-empty continuum;
* `AtMostTwoGeneral.lean` — **`atMostTwo_of_no_separation`**: at most two components, given that no
  proper subcontinuum of the trace separates the plane;
* `MainGeneral.lean` — `NoSeparationOfSubcontinuum` (that hypothesis, as a `Prop`) and the
  conditional statements;
* `subcontinuum_trace_interval.lean` — a compact connected *proper* subset of the trace of a simple
  closed curve is `γ '' Icc a b` with `b - a < 2π`;
* `arc_not_separate.lean` — **an arc does not separate the plane**;
* `NoSeparation.lean` — the two above **discharge `NoSeparationOfSubcontinuum`**;
* `ind_eq_zero_of_avoiding_extension.lean` — **the argument principle in the form needed here**:
  if the curve extends over the disc avoiding a point `x`, then `ind c x = 0` (equivalently: the
  winding number is invariant under homotopies of loops in `ℂ ∖ {x}`); this is what reduces
  `PlaneSchoenflies` to the existence of an *injective* extension of the parametrisation (see
  `SCHOENFLIES.md`);
* `planeSchoenflies_of_injective_extension.lean` — **Schoenflies from an injective extension**:
  an injective continuous `F : 𝔻 → ℂ` agreeing with `c` on the boundary circle automatically has
  `Set.range F = closure S.V`; the (⟸) direction of the equivalence recorded in `SCHOENFLIES.md`;
* `SchoenfliesReduction.lean` — the packaged form of that equivalence: `ExtensionInput` (E),
  `SchoenfliesInput`/`PlaneJordanSchoenflies`/`ClassicalInput` from (E) at `C¹` curves, and the
  converse; so the whole remaining gap of the chapter is the single classical statement (E);
* `Unconditional.lean` — **the unconditional main results** (`jordanSeparation_of_isSimple`,
  `planeSeparation_of_contDiff_of_isSimple`, `jordanInput_of_contDiff`, the index corollaries, the
  frontier/closure statements, and `planeJordanSchoenflies_of_planeSchoenflies`).
-/
