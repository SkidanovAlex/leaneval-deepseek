import Mathlib
import Submission.RiemannSurface
import Submission.Commons.Geometry.Manifold.chart_transition_analyticOnNhd

/-!
# A continuous global phase with a single simple zero at `z₀` (the "degree-one phase")

This file builds, on a connected non-compact Riemann surface `X`, a continuous `Θ : X → ℂ`
which is nowhere zero off `z₀` and has a *simple* zero at `z₀` in the chart at `z₀`.  The
construction is the classical "telescoping chain to infinity":

* an escaping sequence of pivots `a 0 = z₀, a 1, a 2, …` with consecutive pivots in a common
  chart ball and with locally finitely many such balls (`Work.Drive.exists_phase_chain`);
* the *transfer gadget* `g i`, supported in the `i`-th ball, equal to the phase of
  `(z - z(a i)) / (z - z(a (i+1)))` near the pivots and cut off to `1` near the boundary of the
  ball (the cutoff interpolant is the explicit series `∑ u^n/n = -log (1-u)`);
* the locally finite product `∏ᵢ g i`, whose windings cancel at every intermediate pivot, and
  which therefore has total winding one at `z₀`;
* the radial factor `m`, equal to `‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖` near `z₀`, which turns
  that winding-one phase into an honest simple zero.

The pivot values of the product are filled in by the limit of the product along the punctured
neighbourhood of the pivot (`Filter.limUnder`), which exists because the chart transition of a
complex one-manifold is analytic (`Commons.Geometry.Manifold.chart_transition_analyticOnNhd`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

/-- The formal logarithmic series `∑ uⁿ/n`, converging for `‖u‖ < 1` to `-log (1-u)`. -/
def logSeries (u : ℂ) : ℂ := ∑' n : ℕ, u ^ n / n

lemma exp_neg_logSeries {u : ℂ} (hu : ‖u‖ < 1) : Complex.exp (-(logSeries u)) = 1 - u := by
  rw [logSeries, (Complex.hasSum_taylorSeries_neg_log hu).tsum_eq, neg_neg]
  refine Complex.exp_log (fun h => ?_)
  have hu1 : u = 1 := by
    have h2 := congrArg (fun z : ℂ => (1 : ℂ) - z) h
    simpa using h2
  rw [hu1, norm_one] at hu
  exact lt_irrefl 1 hu

lemma logSeries_of_norm_lt_one {u : ℂ} (hu : ‖u‖ < 1) : logSeries u = -Complex.log (1 - u) := by
  rw [logSeries, (Complex.hasSum_taylorSeries_neg_log hu).tsum_eq]

/-- `logSeries` is continuous on the open unit disc (there it is `-log (1 - ·)`). -/
lemma continuousOn_logSeries : ContinuousOn logSeries (Metric.ball (0 : ℂ) 1) := by
  intro u hu
  have hu' : ‖u‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hu
  have hmem : (1 - u) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    refine Or.inl ?_
    rw [Complex.sub_re, Complex.one_re]
    linarith [Complex.re_le_norm u]
  have h1 : ContinuousAt (fun v : ℂ => -Complex.log (1 - v)) u :=
    ((continuousAt_const.sub continuousAt_id).clog hmem).neg
  have h2 : logSeries =ᶠ[𝓝 u] fun v : ℂ => -Complex.log (1 - v) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hu] with v hv
    exact logSeries_of_norm_lt_one (by simpa [dist_eq_norm] using Metric.mem_ball.mp hv)
  exact (h1.congr h2.symm).continuousWithinAt

/-! ## The transfer gadget

For a chain of pivots `a : ℕ → X` with radii `ρ`, the `i`-th gadget is supported in the chart
ball of radius `8 ρ i` around `a i`; near the two pivots it equals the phase of the ratio of chart
differences `(z - z(a i)) / (z - z(a (i+1)))`, and in the annulus `2 ρ i ≤ ‖·‖ ≤ 8 ρ i` it is
interpolated to the constant `1` by the explicit logarithmic series. -/

/-- The unit phase `z/‖z‖` of a complex number (junk value `0` at `0`). -/
def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

@[simp] lemma phase_zero : phase 0 = 0 := by
  simp [phase]

lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  have h : r * r = |r| * |r| := (abs_mul_abs_self r).symm
  rw [h, Real.sqrt_mul_self (abs_nonneg r)]

lemma norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  have h : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp only [phase]
  rw [norm_div, norm_ofReal_complex, abs_of_nonneg (norm_nonneg z), div_self h]

lemma phase_mul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) : phase z * phase w = phase (z * w) := by
  simp only [phase, norm_mul, Complex.ofReal_mul]
  rw [div_mul_div_comm]

lemma phase_ne_zero {z : ℂ} (hz : z ≠ 0) : phase z ≠ 0 := by
  intro h
  have := norm_phase hz
  rw [h, norm_zero] at this
  exact zero_ne_one this

section Gadget

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The image of the first pivot of the `i`-th gadget, in the chart at `a i`. -/
def gP (a : ℕ → X) (i : ℕ) : ℂ := (chartAt ℂ (a i)) (a i)

/-- The image of the second pivot of the `i`-th gadget, in the chart at `a i`. -/
def gQ (a : ℕ → X) (i : ℕ) : ℂ := (chartAt ℂ (a i)) (a (i + 1))

/-- The cutoff that sends the interpolating exponent to `0` at the boundary of the support. -/
def gCut (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) (x : X) : ℝ :=
  max 0 (min 1 ((8 * ρ i - ‖(chartAt ℂ (a i)) x - gP a i‖) / (6 * ρ i)))

/-- The series argument of the `i`-th gadget, meaningful where `‖(gQ - gP)/(c x - gP)‖ < 1`. -/
def gArg (a : ℕ → X) (i : ℕ) (x : X) : ℂ :=
  logSeries ((gQ a i - gP a i) / ((chartAt ℂ (a i)) x - gP a i))

/-- The `i`-th transfer gadget. -/
def gadget (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) : X → ℂ :=
  fun x =>
    if x ∈ (chartAt ℂ (a i)).source ∧ ‖(chartAt ℂ (a i)) x - gP a i‖ ≤ 2 * ρ i then
      phase (((chartAt ℂ (a i)) x - gP a i) / ((chartAt ℂ (a i)) x - gQ a i))
    else if x ∈ (chartAt ℂ (a i)).source ∧ ‖(chartAt ℂ (a i)) x - gP a i‖ < 8 * ρ i then
      Complex.exp (Complex.I * ((gCut a ρ i x : ℂ) * ((gArg a i x).im : ℂ)))
    else 1

lemma gCut_nonneg (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) (x : X) : 0 ≤ gCut a ρ i x :=
  le_max_left _ _

lemma gCut_le_one (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) (x : X) : gCut a ρ i x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- Away from the two pivots the gadget is a unit complex number. -/
lemma norm_gadget_eq_one {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X}
    (hsrc : a (i + 1) ∈ (chartAt ℂ (a i)).source)
    (hx₁ : x ≠ a i) (hx₂ : x ≠ a (i + 1)) : ‖gadget a ρ i x‖ = 1 := by
  unfold gadget
  by_cases h1 : x ∈ (chartAt ℂ (a i)).source ∧ ‖(chartAt ℂ (a i)) x - gP a i‖ ≤ 2 * ρ i
  · rw [if_pos h1]
    have hxs : x ∈ (chartAt ℂ (a i)).source := h1.1
    have hnum : (chartAt ℂ (a i)) x - gP a i ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      exact hx₁ ((chartAt ℂ (a i)).injOn hxs (mem_chart_source ℂ (a i)) h)
    have hden : (chartAt ℂ (a i)) x - gQ a i ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      exact hx₂ ((chartAt ℂ (a i)).injOn hxs hsrc h)
    have hr : ((chartAt ℂ (a i)) x - gP a i) / ((chartAt ℂ (a i)) x - gQ a i) ≠ 0 :=
      div_ne_zero hnum hden
    exact norm_phase hr
  · rw [if_neg h1]
    by_cases h2 : x ∈ (chartAt ℂ (a i)).source ∧ ‖(chartAt ℂ (a i)) x - gP a i‖ < 8 * ρ i
    · rw [if_pos h2, Complex.norm_exp]
      simp
    · rw [if_neg h2, norm_one]

/-- The gadget is `1` outside the chart ball of radius `8 ρ i`. -/
lemma gadget_eq_one_of_far {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X}
    (hρ : 0 < ρ i) (h : ¬ (x ∈ (chartAt ℂ (a i)).source ∧
      ‖(chartAt ℂ (a i)) x - gP a i‖ < 8 * ρ i)) : gadget a ρ i x = 1 := by
  unfold gadget
  have h1 : ¬ (x ∈ (chartAt ℂ (a i)).source ∧
      ‖(chartAt ℂ (a i)) x - gP a i‖ ≤ 2 * ρ i) :=
    fun hh => h ⟨hh.1, lt_of_le_of_lt hh.2 (by linarith)⟩
  rw [if_neg h1, if_neg h]

/-- In the inner region the gadget is exactly the phase of the ratio of the two chart differences. -/
lemma gadget_eq_phase {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X}
    (h : x ∈ (chartAt ℂ (a i)).source ∧ ‖(chartAt ℂ (a i)) x - gP a i‖ ≤ 2 * ρ i) :
    gadget a ρ i x = phase (((chartAt ℂ (a i)) x - gP a i) / ((chartAt ℂ (a i)) x - gQ a i)) := by
  unfold gadget
  rw [if_pos h]

/-- Where the gadget differs from `1`, the point lies in the chart ball of radius `8 ρ i`. -/
lemma gadget_ne_one_mem {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X} (hρ : 0 < ρ i)
    (h : gadget a ρ i x ≠ 1) :
    x ∈ (chartAt ℂ (a i)).source ∧ ‖(chartAt ℂ (a i)) x - gP a i‖ < 8 * ρ i := by
  by_contra hcon
  exact h (gadget_eq_one_of_far hρ hcon)

end Gadget

end Work.Drive
