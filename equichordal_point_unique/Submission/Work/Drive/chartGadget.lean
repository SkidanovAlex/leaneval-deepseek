import Mathlib
import Submission.RiemannSurface
import Submission.Work.Drive.phaseGadget

/-!
# The transfer gadget attached to a *chosen* chart family

`Submission/Work/Drive/phaseGadget.lean` builds the transfer gadgets `Work.Drive.gadget a ρ i`
using the preferred chart `chartAt ℂ (a i)`.  For the construction of the global degree-one phase
this is not enough: `ChartedSpace.chartAt` is arbitrary chosen data, and there are legitimate
complex-chart structures on a surface in which `(chartAt ℂ x).source` is trapped in a small set
(see the counterexample `Work.Drive.no_chain_counterexample`).  The escaping chain therefore has to
be produced together with a *chart family* `c : ℕ → OpenPartialHomeomorph X ℂ` taken from the
maximal atlas, and all of the gadget theory has to be phrased for that family.

This file repeats the definitions and the elementary algebraic lemmas of `phaseGadget.lean` with
`chartAt ℂ (a i)` replaced by `c i`; the proofs are the same, the only extra inputs being
`a i ∈ (c i).source` and `a (i + 1) ∈ (c i).source` (used to know that `c i` is injective on the
two pivots).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

section ChartGadget

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The image of the first pivot of the `i`-th gadget, in the chosen chart `c i`. -/
def chP (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (i : ℕ) : ℂ := (c i) (a i)

/-- The image of the second pivot of the `i`-th gadget, in the chosen chart `c i`. -/
def chQ (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (i : ℕ) : ℂ := (c i) (a (i + 1))

/-- The cutoff that sends the interpolating exponent to `0` at the boundary of the support. -/
def chCut (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) (x : X) : ℝ :=
  max 0 (min 1 ((8 * ρ i - ‖(c i) x - chP c a i‖) / (6 * ρ i)))

/-- The series argument of the `i`-th gadget, meaningful where `‖(q - p)/(c i x - p)‖ < 1`. -/
def chArg (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (i : ℕ) (x : X) : ℂ :=
  logSeries ((chQ c a i - chP c a i) / ((c i) x - chP c a i))

/-- The `i`-th transfer gadget, in the chosen chart `c i`. -/
def chGadget (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) : X → ℂ :=
  fun x =>
    if x ∈ (c i).source ∧ ‖(c i) x - chP c a i‖ ≤ 2 * ρ i then
      phase (((c i) x - chP c a i) / ((c i) x - chQ c a i))
    else if x ∈ (c i).source ∧ ‖(c i) x - chP c a i‖ < 8 * ρ i then
      Complex.exp (Complex.I * ((chCut c a ρ i x : ℂ) * ((chArg c a i x).im : ℂ)))
    else 1

/-- The `8 ρ i`-ball of the `i`-th gadget, in the chosen chart `c i`. -/
def chBall (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) : Set X :=
  {x : X | x ∈ (c i).source ∧ (c i) x ∈ Metric.ball ((c i) (a i)) (8 * ρ i)}

/-- The set of indices whose gadget differs from `1` at `x`. -/
def chActive (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (ρ : ℕ → ℝ) (x : X) : Set ℕ :=
  {i : ℕ | x ∈ chBall c a ρ i}

lemma mem_chBall {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X} :
    x ∈ chBall c a ρ i ↔ x ∈ (c i).source ∧ ‖(c i) x - (c i) (a i)‖ < 8 * ρ i := by
  simp [chBall, Metric.mem_ball, dist_eq_norm]

lemma chCut_nonneg (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) (x : X) :
    0 ≤ chCut c a ρ i x :=
  le_max_left _ _

lemma chCut_le_one (c : ℕ → OpenPartialHomeomorph X ℂ) (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) (x : X) :
    chCut c a ρ i x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- Away from the two pivots the gadget is a unit complex number. -/
lemma norm_chGadget_eq_one {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ}
    {x : X} (hP : a i ∈ (c i).source) (hQ : a (i + 1) ∈ (c i).source)
    (hx₁ : x ≠ a i) (hx₂ : x ≠ a (i + 1)) : ‖chGadget c a ρ i x‖ = 1 := by
  unfold chGadget
  by_cases h1 : x ∈ (c i).source ∧ ‖(c i) x - chP c a i‖ ≤ 2 * ρ i
  · rw [if_pos h1]
    have hxs : x ∈ (c i).source := h1.1
    have hnum : (c i) x - chP c a i ≠ 0 := by
      intro h
      rw [chP, sub_eq_zero] at h
      exact hx₁ ((c i).injOn hxs hP h)
    have hden : (c i) x - chQ c a i ≠ 0 := by
      intro h
      rw [chQ, sub_eq_zero] at h
      exact hx₂ ((c i).injOn hxs hQ h)
    have hr : ((c i) x - chP c a i) / ((c i) x - chQ c a i) ≠ 0 := div_ne_zero hnum hden
    exact norm_phase hr
  · rw [if_neg h1]
    by_cases h2 : x ∈ (c i).source ∧ ‖(c i) x - chP c a i‖ < 8 * ρ i
    · rw [if_pos h2, Complex.norm_exp]
      simp
    · rw [if_neg h2, norm_one]

/-- The gadget is `1` outside the chart ball of radius `8 ρ i`. -/
lemma chGadget_eq_one_of_far {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ}
    {x : X} (hρ : 0 < ρ i) (h : ¬ (x ∈ (c i).source ∧
      ‖(c i) x - chP c a i‖ < 8 * ρ i)) : chGadget c a ρ i x = 1 := by
  unfold chGadget
  have h1 : ¬ (x ∈ (c i).source ∧ ‖(c i) x - chP c a i‖ ≤ 2 * ρ i) :=
    fun hh => h ⟨hh.1, lt_of_le_of_lt hh.2 (by linarith)⟩
  rw [if_neg h1, if_neg h]

/-- In the inner region the gadget is exactly the phase of the ratio of the two chart differences. -/
lemma chGadget_eq_phase {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ}
    {x : X} (h : x ∈ (c i).source ∧ ‖(c i) x - chP c a i‖ ≤ 2 * ρ i) :
    chGadget c a ρ i x = phase (((c i) x - chP c a i) / ((c i) x - chQ c a i)) := by
  unfold chGadget
  rw [if_pos h]

/-- Where the gadget differs from `1`, the point lies in the chart ball of radius `8 ρ i`. -/
lemma chGadget_ne_one_mem {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ}
    {x : X} (hρ : 0 < ρ i) (h : chGadget c a ρ i x ≠ 1) :
    x ∈ (c i).source ∧ ‖(c i) x - (c i) (a i)‖ < 8 * ρ i := by
  rw [← mem_chBall]
  by_contra hcon
  exact h (chGadget_eq_one_of_far hρ (fun hh => hcon (mem_chBall.mpr hh)))

end ChartGadget

end Work.Drive
