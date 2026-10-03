import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Deps
import Submission.Lib.Unif2.Work.Parabolic.isCompact_closure_superlevel_greenUpperHalfPlane

/-!
# The upper half plane has a Green function at `i`

This module proves `Work.Parabolic.hasGreenFunctionAt_iUHP`, the statement that the classical
function

`greenUpperHalfPlane w = log (‖w + i‖ / ‖w - i‖)`  (`Submission/Work/Parabolic/Model.lean`)

is a Green function of the upper half plane `ℍ` in the relative-compactness sense of
`Work.Parabolic.IsGreenFunctionAt` (`Submission/Work/Parabolic/Basic.lean`): strictly positive off
the pole, harmonic off the pole, and with relatively compact superlevel sets.

The three ingredients, in the order in which they are used below:

* `greenUpperHalfPlane_pos` — positivity off the pole, from `‖w + i‖ > ‖w - i‖` for `w ∈ ℍ`;
* `harmonicOnXAt_greenUpperHalfPlane` — harmonicity.  The chart of `ℍ` at any point is the
  inclusion `ℍ ↪ ℂ` with inverse `UpperHalfPlane.ofComplex`, so
  `HarmonicOnXAt u x` unfolds to `InnerProductSpace.HarmonicAt (u ∘ ofComplex) (x : ℂ)`, and
  `greenUpperHalfPlane ∘ ofComplex` agrees near `(x : ℂ)` (which has positive imaginary part)
  with `greenUpperHalfPlaneC z = log (‖z + i‖ / ‖z - i‖) = log ‖z + i‖ - log ‖z - i‖`, harmonic
  off `i` by `AnalyticAt.harmonicAt_log_norm`;
* `Work.Parabolic.isCompact_closure_superlevel_greenUpperHalfPlane` (proved in the module of the
  same name next to this one) — relative compactness of the superlevel sets, an elementary
  two-sided estimate showing that `{w | ε ≤ greenUpperHalfPlane w}` lies in the compact Apollonius
  disc `{w | δ ≤ (w : ℂ).im, ‖(w : ℂ) - i‖ ≤ r}` with `δ = (e^ε - 1)/(e^ε + 1)`,
  `r = 2/(e^ε - 1)`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.Parabolic

/-! ## Positivity off the pole -/

/-- The model Green function of the upper half plane is strictly positive away from its pole:
for `w = a + bi ∈ ℍ`, the squared distances to `i` and to `-i` are `a² + (b-1)²` and `a² + (b+1)²`,
so `‖w + i‖ > ‖w - i‖`. -/
theorem greenUpperHalfPlane_pos {w : UpperHalfPlane} (hw : w ≠ iUHP) :
    0 < greenUpperHalfPlane w := by
  have hw' : (w : ℂ) ≠ Complex.I := fun h => hw (UpperHalfPlane.ext h)
  have hnsI : Complex.normSq ((w : ℂ) + Complex.I)
      = Complex.normSq (w : ℂ) + 2 * (w : ℂ).im + 1 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
    ring
  have hnsm : Complex.normSq ((w : ℂ) - Complex.I)
      = Complex.normSq (w : ℂ) - 2 * (w : ℂ).im + 1 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    ring
  have hlt_ns : Complex.normSq ((w : ℂ) - Complex.I) < Complex.normSq ((w : ℂ) + Complex.I) := by
    rw [hnsI, hnsm]
    linarith [UpperHalfPlane.coe_im_pos w]
  have hlt2 : ‖(w : ℂ) - Complex.I‖ ^ 2 < ‖(w : ℂ) + Complex.I‖ ^ 2 := by
    simpa [Complex.normSq_eq_norm_sq] using hlt_ns
  have hlt : ‖(w : ℂ) - Complex.I‖ < ‖(w : ℂ) + Complex.I‖ :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hlt2
  have hb : 0 < ‖(w : ℂ) - Complex.I‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw')
  have hplus : (w : ℂ) + Complex.I ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; linarith [norm_nonneg ((w : ℂ) - Complex.I)]
  rw [greenUpperHalfPlane,
    Real.log_div (norm_ne_zero_iff.mpr hplus) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw'))]
  have := Real.log_lt_log hb hlt
  linarith

/-! ## Harmonicity -/

/-- **The planar model Green function is harmonic off its pole.**  For `z` in the upper half
plane other than `i`, `greenUpperHalfPlaneC z = log (‖z + i‖ / ‖z - i‖)` agrees with
`log ‖z + i‖ - log ‖z - i‖` near `z`, a difference of two functions of the form `log ‖f‖` with `f`
analytic and nonvanishing (`AnalyticAt.harmonicAt_log_norm`). -/
theorem harmonicAt_greenUpperHalfPlaneC {z : ℂ} (hz : 0 < z.im) (hne : z ≠ Complex.I) :
    InnerProductSpace.HarmonicAt greenUpperHalfPlaneC z := by
  have hne' : z - Complex.I ≠ 0 := sub_ne_zero.mpr hne
  have hneg : z ≠ -Complex.I := by
    intro h; have h2 := congrArg Complex.im h; simp at h2; linarith [hz]
  have hplus : z + Complex.I ≠ 0 := by
    intro h; have h2 := congrArg Complex.im h; simp at h2; linarith [hz]
  have hharm : InnerProductSpace.HarmonicAt
      (fun w : ℂ => Real.log ‖w + Complex.I‖ - Real.log ‖w - Complex.I‖) z :=
    (((analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z).add analyticAt_const).harmonicAt_log_norm
        (by simpa using hplus)).sub
      (((analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z).sub analyticAt_const).harmonicAt_log_norm
        (by simpa using hne'))
  have hev : greenUpperHalfPlaneC =ᶠ[𝓝 z]
      (fun w : ℂ => Real.log ‖w + Complex.I‖ - Real.log ‖w - Complex.I‖) := by
    filter_upwards [(isOpen_ne (x := Complex.I)).mem_nhds hne,
      (isOpen_ne (x := -Complex.I)).mem_nhds hneg] with w hw1 hw2
    have h1 : w - Complex.I ≠ 0 := sub_ne_zero.mpr hw1
    have h2 : w + Complex.I ≠ 0 := fun h => hw2 (add_eq_zero_iff_eq_neg.mp h)
    rw [greenUpperHalfPlaneC, Real.log_div (norm_ne_zero_iff.mpr h2) (norm_ne_zero_iff.mpr h1)]
  rw [InnerProductSpace.harmonicAt_congr_nhds hev]
  exact hharm

/-- **`greenUpperHalfPlane` is harmonic off its pole, in the sense of `HarmonicOnXAt`.**

The chart of `ℍ` at `x` is the open embedding `ℍ ↪ ℂ` (the `singletonChartedSpace` of
`UpperHalfPlane.isOpenEmbedding_coe`), whose inverse is `UpperHalfPlane.ofComplex`; hence
`HarmonicOnXAt u x = InnerProductSpace.HarmonicAt (u ∘ ofComplex) (x : ℂ)`.  The composite
`greenUpperHalfPlane ∘ ofComplex` agrees near `(x : ℂ)` — an open condition, as `(x : ℂ).im > 0` —
with `greenUpperHalfPlaneC`. -/
theorem harmonicOnXAt_greenUpperHalfPlane {x : UpperHalfPlane} (hne : x ≠ iUHP) :
    Submission.HarmonicOnXAt greenUpperHalfPlane x := by
  have hx : (x : ℂ) ≠ Complex.I := fun h => hne (UpperHalfPlane.ext h)
  have hz : 0 < (x : ℂ).im := UpperHalfPlane.coe_im_pos x
  have hzi : 0 < x.im := by rw [← UpperHalfPlane.coe_im]; exact hz
  have hev : (greenUpperHalfPlane ∘ UpperHalfPlane.ofComplex)
      =ᶠ[𝓝 ((x : ℂ))] greenUpperHalfPlaneC := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with z hz'
    rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    rfl
  rw [show Submission.HarmonicOnXAt greenUpperHalfPlane x
      = InnerProductSpace.HarmonicAt (greenUpperHalfPlane ∘ UpperHalfPlane.ofComplex) ((x : ℂ))
      from rfl]
  rw [InnerProductSpace.harmonicAt_congr_nhds hev]
  have hplus : (x : ℂ) + Complex.I ≠ 0 := by
    intro h; have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at h2
    linarith [hzi]
  have hne' : (x : ℂ) - Complex.I ≠ 0 := sub_ne_zero.mpr hx
  have hneg : (x : ℂ) ≠ -Complex.I := by
    intro h; have h2 := congrArg Complex.im h
    simp only [Complex.neg_im, Complex.I_im] at h2
    linarith [hzi]
  have hharm : InnerProductSpace.HarmonicAt
      (fun w : ℂ => Real.log ‖w + Complex.I‖ - Real.log ‖w - Complex.I‖) ((x : ℂ)) :=
    (((analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) ((x : ℂ))).add analyticAt_const).harmonicAt_log_norm
        (by simpa using hplus)).sub
      (((analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) ((x : ℂ))).sub analyticAt_const).harmonicAt_log_norm
        (by simpa using hne'))
  have hev2 : greenUpperHalfPlaneC =ᶠ[𝓝 ((x : ℂ))]
      (fun w : ℂ => Real.log ‖w + Complex.I‖ - Real.log ‖w - Complex.I‖) := by
    filter_upwards [(isOpen_ne (x := Complex.I)).mem_nhds hx,
      (isOpen_ne (x := -Complex.I)).mem_nhds hneg] with w hw1 hw2
    have h1 : w - Complex.I ≠ 0 := sub_ne_zero.mpr hw1
    have h2 : w + Complex.I ≠ 0 := fun h => hw2 (add_eq_zero_iff_eq_neg.mp h)
    rw [greenUpperHalfPlaneC, Real.log_div (norm_ne_zero_iff.mpr h2) (norm_ne_zero_iff.mpr h1)]
  rw [InnerProductSpace.harmonicAt_congr_nhds hev2]
  exact hharm

/-! ## The Green function -/

/-- **The upper half plane has a Green function at `i`.**  Witness: the classical
`Work.Parabolic.greenUpperHalfPlane w = log (‖w + i‖ / ‖w - i‖)` (`Model.lean`), whose superlevel
sets are Apollonius discs strictly inside `ℍ`, so their closures are compact; and whose pullback to
a chart of `ℍ` is `z ↦ log ‖z + i‖ - log ‖z - i‖`, harmonic off `i`. -/
theorem hasGreenFunctionAt_iUHP :
    Work.Parabolic.HasGreenFunctionAt (X := UpperHalfPlane) Work.Parabolic.iUHP := by
  refine ⟨greenUpperHalfPlane, ?_, ?_, ?_⟩
  · intro w hw
    exact greenUpperHalfPlane_pos hw
  · intro x hx
    exact harmonicOnXAt_greenUpperHalfPlane (by simpa using hx)
  · intro ε hε
    exact isCompact_closure_superlevel_greenUpperHalfPlane hε

end Work.Parabolic
