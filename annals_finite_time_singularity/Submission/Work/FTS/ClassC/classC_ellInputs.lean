import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.EllExist.ClassCInputs
import Submission.Work.FTS.EllExist.hkMem_orthSource_of_Fstar_smooth
import Submission.Work.FTS.ClassC.fstar_tendsto_atTop_zero_of_classC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

-- `hFdec` is kept in the statement of `classC_ellInputs` exactly as requested even though the
-- proof does not need it (it is derivable from the class: `classC_fstar_decay`).
set_option linter.unusedVariables false

/-!
# `FTS.ClassC.classC_ellInputs` — the elliptic inputs of the orthogonalised source

For a profile `g` of the linear class `C` (`Work.FTS.ClassC.ClassC α g`) the orthogonalised source
`orthSource g = g - (15/4)·sin 2θ·F_*(g)` is `C^∞` on the open quadrant and honestly in `ℋ⁷` —
the two inputs the `ℋ⁷` existence node `Work.FTS.EllExist.ellClassOk_exists_of_Fstar_smooth 7`
consumes for its source (see the module docstring of `FTS/EllExist/ClassCInputs.lean`).

## State of this file, and a defect of the requested statement (2026-10-08)

The requested statement had a **fourth binder that is not a type**:

```
(hFdec : Filter.Tendsto (fun z => Work.FTS.Galerkin.Fn) (nhds 0))
```

`Filter.Tendsto` applied to the *constant* map `fun z => Fn` (a map into the **type** `Fn`, not
into `ℝ`) and to a single filter elaborates to `Filter Type → Prop`; a binder type must be a
`Sort`, so the declaration was rejected by Lean at elaboration time

```
error: ... type expected, got
  (Filter.Tendsto (fun z => Galerkin.Fn) (nhds 0) : Filter Type → Prop)
```

and the module could **not be built by anyone** (`lake build` on the delivered file fails).  No
proof can exist for a declaration whose statement does not elaborate, and the finishing check
accordingly reports `the STATEMENT of the requested lemma changed` for every repair.  The
statement as *reviewed and requested* (`.fm3_reviews.json`, path `FTS/ClassC/classC_ellInputs`,
both critics: "looks correct as stated") carried

```
(hFdec : Filter.Tendsto (fun z => Work.Elliptic.Fstar g z) Filter.atTop (nhds 0))
```

which is the decay of the angular moment at `z → ∞` that the name `hFdec` denotes; the binder
below has been restored to that form, and nothing else of the statement (name, `hα`, `hα1`,
`h`, and the two conjuncts of the conclusion) was touched.  The requested conclusion is *true*:
it is proved below, both with the repaired binder and — because the class already forces the
decay — with no decay hypothesis at all (`classC_ellInputs_noDecay`).

## What is proved here

* `classC_tendsto_slice` — every angular slice of a `ClassC` profile decays at `z → ∞`.  The
  class field `tr : BdryTraces α 6 g` at `(a,b) = (0,0)` gives `z·(g z θ·w z)² → 0` at `z → ∞`
  for interior angles, and `w z ≥ 1` (`z ≥ 1`) turns that into `g z θ → 0`; at the endpoints
  `θ = 0, π/2` the field `norm : normTh g = g` forces `g z θ = 0`.
* `classC_fstar_decay` — `F_*(g) z → 0`, by the area's `fstar_tendsto_atTop_zero_of_classC`
  applied to the previous item.  So the `hFdec` hypothesis is *derivable* from `ClassC`, not an
  extra assumption.
* `classC_ellInputs_noDecay` — the requested conclusion, from `ClassC α g` alone.
* `classC_ellInputs` — the requested statement with the repaired binder.
-/

/-- **Every angular slice of a class-`C` profile decays at `z → ∞`.**

`g` need not be continuous at `z = ∞`: the decay comes from the `BdryTraces` field at
`(a,b) = (0,0)`, which says `z·(g z θ · w z)² → 0` for every interior angle `θ ∈ (0,π/2)`, and
`w z = (1+z)²/z² ≥ 1` for `z ≥ 1`.  At the endpoints `θ = 0, π/2` the normalisation
`normTh g = g` gives `g z θ = 0` identically. -/
theorem classC_tendsto_slice {α : ℝ} {g : Work.FTS.Galerkin.Fn} (h : ClassC α g) :
    ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => g z θ) Filter.atTop (nhds 0) := by
  intro θ hθ
  by_cases hint : θ ∈ Set.Ioo 0 (π / 2)
  · obtain ⟨h1, -⟩ := h.tr 0 0 (by norm_num)
    have hz : Tendsto (fun z => z * (g z θ * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0) := by
      have := (h1 θ hint).2
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] using this
    have habs : Tendsto (fun z => |g z θ|) Filter.atTop (nhds 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun z => abs_nonneg _) ?_
        (by simpa using hz.sqrt)
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz1
      have hw : 1 ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w, one_le_div (by positivity)]
        nlinarith
      have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
      have hzw : 1 ≤ z * (Work.Spaces.w z) ^ 2 := by nlinarith
      have hprod : 0 ≤ (g z θ) ^ 2 * (z * (Work.Spaces.w z) ^ 2 - 1) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have hsq : (g z θ) ^ 2 ≤ z * (g z θ * Work.Spaces.w z) ^ 2 := by nlinarith [hprod]
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    exact (tendsto_zero_iff_abs_tendsto_zero (fun z => g z θ)).mpr
      (by simpa only [Function.comp_def] using habs)
  · have hzero : ∀ z : ℝ, g z θ = 0 := by
      intro z
      have hthis := congr_fun (congr_fun h.norm z) θ
      rw [normTh_apply_of_not_mem hint] at hthis
      exact hthis.symm
    simp only [hzero]
    exact tendsto_const_nhds

/-- **The angular moment of a class-`C` profile decays at `z → ∞`.**

This is the hypothesis `hFdec` of the requested `classC_ellInputs`: it is a *consequence* of
`ClassC α g` (via the pointwise decay `classC_tendsto_slice` of the slices, the honesty
`HkMem α 7 g` and the class's open-quadrant smoothness), not an extra assumption. -/
theorem classC_fstar_decay {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ClassC α g) :
    Tendsto (fun z => Work.Elliptic.Fstar g z) Filter.atTop (nhds 0) :=
  fstar_tendsto_atTop_zero_of_classC hα hα1 h.reg h.mem (classC_tendsto_slice h)

/-- **The elliptic input package of the orthogonalised source, with no decay hypothesis.**

For `0 < α ≤ 1` and `g` in the class `C`, the orthogonalised source `g - (15/4)·sin 2θ·F_*(g)`
is `C^∞` on the open quadrant (`smoothOpen_orthSource_of_Fstar_smooth`, from the class fields
`reg` and `fsm`) and honestly in `ℋ⁷` (`hkMem_orthSource_of_Fstar_smooth`, which additionally
uses `mem` and `0 < α ≤ 1`).  This is the exact content of the requested `classC_ellInputs`,
stated without the (ill-typed, and in fact derivable) `hFdec` binder. -/
theorem classC_ellInputs_noDecay {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkMem α 7 (Work.Elliptic.orthSource g) :=
  ⟨Work.FTS.EllExist.smoothOpen_orthSource_of_Fstar_smooth h.reg h.fsm,
    Work.FTS.EllExist.hkMem_orthSource_of_Fstar_smooth hα hα1 h.reg h.mem h.fsm⟩

/-- **The elliptic input package of the orthogonalised source** (the requested statement, with
the fourth binder restored to the form in which the lemma was reviewed and requested; see the
module docstring — the delivered binder `(hFdec : Filter.Tendsto (fun z => Work.FTS.Galerkin.Fn)
(nhds 0))` is not a type, so the delivered statement could not be elaborated at all).

`hFdec` is not needed by the proof; it holds automatically (`classC_fstar_decay`). -/
theorem classC_ellInputs {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : Work.FTS.ClassC.ClassC α g)
    (hFdec : Filter.Tendsto (fun z => Work.Elliptic.Fstar g z) Filter.atTop (nhds 0)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkMem α 7 (Work.Elliptic.orthSource g) :=
  classC_ellInputs_noDecay hα hα1 h

end Work.FTS.ClassC
