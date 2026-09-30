/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — charts of the Jacobian drive: the definitions and the named inputs

Import this module for the *definitions* of area `CH` (`NOTES_LEAD_jacobian_GC.md` §3.5) and
the named inputs it builds on; the *proved* lemmas of the area are one per file and are all
imported by `Submission.Work.Charts.All`.  See `Submission/Work/Charts/NOTES.md` for the full
description, the list of named inputs and the status of each item.

## Files of this area

* `Submission.Work.Charts.Basic` — the conventions of the area (`Sym`, `divOf`, `pullK`,
  `iOf`), the Riemann–Roch input `RochData` (RR5 built into `iOf`, plus the Riemann–Roch
  equation and RR7), the scheme-theoretic input `SymProps`, and the Brill–Noether chart
  `BNData` with its open subscheme `V`, its affineness, the fact that `ℓ = 1` on its points,
  and the uniqueness of the chart point in its linear equivalence class;
* `Submission.Work.Charts.ChartCg` — the Brill–Noether chart built on the `g`-fold product
  `C^g` instead of on the affine chart `Sym^g(U)` of area `SY`: the quotient map
  `quotMap : C^g ⟶ Sym^g C`, the product open `U^g`, the determinant section
  `bnDelta = det (h_j(x_m))²` on it, the evaluation `evalSection` of a section at a field
  point, and the chart `chartOpen C g U s hclosed = (quotMap '' (C^g ∖ D(δ)))ᶜ` of `Sym^g C`;
* `Submission.Work.Charts.Cover` — the class `chartClass` of a difference of two points of
  `Sym^g C` with its additive API, the chart relation `InChart`, the covering `Charts` (COV)
  and its Galois refinement `GalCharts` (COV′), with the named inputs `HasCharts`,
  `HasGalCharts`, `HasChartBaseChange`;
* `Submission.Work.Charts.Datum` — `ChartDatum`, the chart datum in the shape consumed by
  area `GC` (the CH-fields of `Work.GroupChunk.Input`), and the named input `HasChartDatum`;
* `Submission.Work.Charts.Density` — the geometric inputs of COV: density of separable points
  (`SepClosedDense`, `dense_sepClosed_points`), density of `K`-points in the base change
  (`PointsDenseAfterBaseChange`, `dense_points_extension`), GENERIC′ (`GenericTranslate`,
  `generic_translate`) and the base change of the chart (`ChartBaseChange`, `V_base_change`).

## Proved lemmas (delegated to the fleet, all in this directory)

  chart `V` is a coordinate chart: the class map on it is injective;
  of the field of definition;
  effective degree-`g` representative of its class;
  containing the generic point;
  covering centre (COV′);
-/
import Submission.Work.Charts.Basic
import Submission.Work.Charts.FinBC
import Submission.Work.Charts.ChartCg
import Submission.Work.Charts.Cover
import Submission.Work.Charts.Datum
import Submission.Work.Charts.Density

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

