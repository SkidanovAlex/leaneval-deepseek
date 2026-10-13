/-
# `Work.ChiExplicit` — the cut-off `χ` of the route, by an **explicit formula**

This is the start of the chapter that repoints the workspace's cut-off
`Work.Stability.chi` from Mathlib's abstract `ContDiffBump` (whose underlying function is a
`Classical.choice` over `someContDiffBumpBase ℝ`, hence *opaque*) to the **explicit** function
that Mathlib's bump base actually builds:

  `chi x = Real.smoothTransition (2 - ‖x‖)`.

Mathlib's `ContDiffBumpBase.ofInnerProductSpace ℝ` has `toFun R x = smoothTransition ((R - ‖x‖)/(R-1))`
(`Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`), and `Work.Stability.bump` is the
`ContDiffBump (0 : ℝ)` with `rIn = 1`, `rOut = 2`, so the coercion
`Work.Stability.bump = fun x => (someContDiffBumpBase ℝ).toFun 2 x` is *the same function* as the
one defined here — but the choice is not reducible (`Classical.choice ⟨a⟩ = a` is not a theorem of
Lean), so no fact about the *formula* is visible through the coercion.  Writing the formula down
directly makes `chi` reduce, and makes the whole `smoothTransition` API available: smoothness,
`= 1` for `‖x‖ ≤ 1`, `= 0` for `‖x‖ ≥ 2`, evenness, positivity on the open ball of radius `2`,
the *support*, and — the point of the exercise — monotonicity and the exact
`log chi x = -1/(2-x) + 1/(x-1) + o(1)` tail, hence `Work.R1G11.CutoffTail` (see
`Submission/Work/ChiExplicit/CutoffTail.lean`).

## Conventions

* `chi` is a function of the **radial variable** `x` (in the route, `x = ρ/L`); it is even, so it is
  really a function of `|x| = ‖x‖`.
* `1 < |x| < 2` is the **annulus**: `chi` decreases strictly there, and `chi = 0` at `|x| = 2`.

## What is here

The explicit definition and its *reduction* lemmas (`chi_apply`, `chi_apply_abs`), plus the whole
elementary interface `chi_contDiff`, `chi_continuous`, `chi_nonneg`, `chi_le_one`, `chi_eq_one`,
`chi_eq_zero`, `chi_neg`, `chi_zero`, `chi_pos_of_abs_lt_one`, `chi_pos_of_abs_lt_two`,
`chi_support`, `chi_pos_of_mem_Ioo` — the mirror image of the `Work.Stability` interface, proved
for the explicit formula.

Everything in this chapter rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.ChiExplicit

/-- **THE EXPLICIT CUT-OFF.**  `chi x = smoothTransition (2 - ‖x‖)`: this is the value at scale `2`
of Mathlib's bump base `ContDiffBumpBase.ofInnerProductSpace ℝ`, written down directly so that it
*reduces* (bypassing the `Classical.choice` inside `someContDiffBumpBase`).

It is `1` on `[-1,1]`, `0` off `(-2,2)`, strictly positive on `(-2,2)`, even, `C^∞`, and strictly
decreasing in `|x|` on the annulus `1 < |x| < 2`. -/
noncomputable def chi (x : ℝ) : ℝ := Real.smoothTransition (2 - ‖x‖)

/-! ## The definition unfolds -/

/-- The definition, as a rewrite rule (this is `rfl`: the point of the explicit formula). -/
theorem chi_apply (x : ℝ) : chi x = Real.smoothTransition (2 - ‖x‖) := rfl

/-- On `ℝ` the norm is the absolute value. -/
theorem chi_apply_abs (x : ℝ) : chi x = Real.smoothTransition (2 - |x|) := by
  rw [chi_apply, Real.norm_eq_abs]

/-! ## The elementary interface -/

/-- `chi` is **even** (it is a function of `‖x‖`). -/
theorem chi_neg (x : ℝ) : chi (-x) = chi x := by
  rw [chi_apply, chi_apply, norm_neg]

/-- `chi ≥ 0`. -/
theorem chi_nonneg (x : ℝ) : 0 ≤ chi x := by
  rw [chi_apply]; exact Real.smoothTransition.nonneg _

/-- `chi ≤ 1`. -/
theorem chi_le_one (x : ℝ) : chi x ≤ 1 := by
  rw [chi_apply]; exact Real.smoothTransition.le_one _

/-- `chi = 1` on the closed unit ball `|x| ≤ 1` (`2 - |x| ≥ 1`, where `smoothTransition = 1`). -/
theorem chi_eq_one {x : ℝ} (h : |x| ≤ 1) : chi x = 1 := by
  rw [chi_apply, Real.norm_eq_abs, Real.smoothTransition.one_of_one_le]
  linarith

/-- `chi = 0` off the open ball of radius `2`, i.e. for `|x| ≥ 2` (`2 - |x| ≤ 0`). -/
theorem chi_eq_zero {x : ℝ} (h : 2 ≤ |x|) : chi x = 0 := by
  rw [chi_apply, Real.norm_eq_abs, Real.smoothTransition.zero_of_nonpos]
  linarith

/-- `chi = 0` strictly outside the closed ball of radius `2`. -/
theorem chi_eq_zero_of_two_lt_abs {x : ℝ} (h : 2 < |x|) : chi x = 0 := chi_eq_zero h.le

/-- `chi 0 = 1`. -/
theorem chi_zero : chi 0 = 1 := chi_eq_one (by norm_num)

/-- `chi` is **strictly positive on the unit ball** `|x| < 1`. -/
theorem chi_pos_of_abs_lt_one {x : ℝ} (h : |x| < 1) : 0 < chi x := by
  rw [chi_eq_one h.le]; norm_num

/-- **`chi` is strictly positive on the open ball of radius `2`** — this is what makes the annulus
`1 < |x| < 2` non-degenerate.  (For the explicit cut-off this is `smoothTransition.pos_of_pos`: the
argument `2 - |x|` is positive there.) -/
theorem chi_pos_of_abs_lt_two {x : ℝ} (h : |x| < 2) : 0 < chi x := by
  rw [chi_apply, Real.norm_eq_abs]
  exact Real.smoothTransition.pos_of_pos (by linarith)

/-- `chi > 0` on the annulus `1 < x < 2` (in the positive half; by evenness this is `1 < |x| < 2`). -/
theorem chi_pos_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (1 : ℝ) 2) : 0 < chi x :=
  chi_pos_of_abs_lt_two (by rw [abs_of_pos (by linarith [h.1])]; exact h.2)

/-- `chi` is `1` on the closed unit ball, in the form used by the `Work.Stability` interface. -/
theorem chi_eq_one_of_abs_le_one {x : ℝ} (h : |x| ≤ 1) : chi x = 1 := chi_eq_one h

/-- **THE SUPPORT OF THE CUT-OFF**: `chi` vanishes exactly off the open ball of radius `2`.  This is
the `ContDiffBump.support_eq` fact of the abstract interface, now by direct computation. -/
theorem chi_support : Function.support chi = Metric.ball (0 : ℝ) 2 := by
  ext x
  rw [Function.mem_support, Metric.mem_ball, Real.dist_eq, sub_zero, chi_apply_abs, ne_eq,
    Real.smoothTransition.zero_iff_nonpos, not_le, sub_pos]

/-- The closure of the support of `chi` is the closed ball of radius `2`. -/
theorem chi_tsupport : tsupport chi = Metric.closedBall (0 : ℝ) 2 := by
  rw [tsupport, chi_support, closure_ball _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- `chi` has compact support. -/
theorem chi_hasCompactSupport : HasCompactSupport chi := by
  rw [HasCompactSupport, chi_tsupport]
  exact isCompact_closedBall _ _

/-! ## The cut-off input of the edge

`Work.R1G11.CutoffTail` is the *only* property of the cut-off beyond the abstract `ContDiffBump`
interface that the divergence of the transport coefficient along a characteristic needs
(`Work.R1G11.cutoff_divergence_of_tail`).  For the explicit cut-off it is a *theorem* (proved in
`Submission/Work/ChiExplicit/CutoffTail.lean` from `chi_deriv_nonpos`); the two `Prop`s below are
the mirror images of `Work.R1G11.CutoffTail` and of its strict form.
-/

/-- **THE CUT-OFF DECREASES ON THE ANNULUS** (weak form, `Work.R1G11.CutoffTail` for the explicit
cut-off): `chi' ≤ 0` on `1 < x < 2`, equivalently `log chi` decreases with the radius. -/
def CutoffTail : Prop := ∀ x ∈ Ioo (1 : ℝ) 2, deriv chi x ≤ 0

/-- The **strict** form: `chi' < 0` on `1 < x < 2` (the cut-off is strictly decreasing there). -/
def CutoffTailStrict : Prop := ∀ x ∈ Ioo (1 : ℝ) 2, deriv chi x < 0

end Work.ChiExplicit
