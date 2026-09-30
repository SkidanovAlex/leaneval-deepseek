import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.Commons.Geometry.Manifold.Tangent.mfderiv_comp_mul_add_apply

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Speed and length of curves

This module starts the metric chapter of the development: it introduces the **speed** of a curve
`γ : ℝ → M` (the norm of its velocity for the Riemannian metric) and the **length** of a curve over
an interval (`intervalIntegral`).

## Main definitions

* `curveSpeed γ t : ℝ` — the Riemannian norm of the velocity `γ'(t)`;
* `curveLength γ a b : ℝ` — the integral of the speed over `[a,b]`.

## Main results

* `curveSpeed_nonneg`, `curveSpeed_sq`, `curveSpeed_const`, `curveLength_const`, `curveLength_self`,
  `curveLength_neg`, `curveLength_nonneg`, `curveLength_add_of_integrable`;
* `curveSpeed_chartCurve` — the chart formula for the speed: for `γ = (extChartAt I x₀).symm ∘ u`
  with `u'(t) = v`, `curveSpeed γ t = √(chartGram x₀ (γ t) v v)`.

## Reparametrisation

* `curveVelocity_comp_mul_add` and `curveSpeed_comp_mul_add` rest on the commons lemma
  `Commons.Geometry.Manifold.Tangent.mfderiv_comp_mul_add_apply`;
* `curveLength_comp_mul_add_of_le` (for `a ≤ b`) and `curveLength_comp_mul_add_of_pos`.

## Next steps in this direction

* the constancy of the speed along a geodesic (`d/dt chartGram x₀ (γ t) (u'(t)) (u'(t)) = 0` for a
  chart geodesic `u`, which uses `hasDerivAt_chartGram_curve` and the geodesic equation), hence
  `curveLength` of the geodesic from `x₀` to `expMap x₀ v` is `‖v‖_{x₀}`.

## Gotchas (learned the hard way)

* The definitions `curveSpeed` and `curveLength` take the model `I` as an *auto*-implicit argument
  (it occurs in their value only), so every use must be written `curveSpeed (I := I) γ t` /
  `curveLength (I := I) γ a b`; and `PwPath`-like declarations must NOT rebind `I` (a parameter
  `(I : ModelWithCorners ℝ E H)` in a definition shadows the section variable and makes all
  instance arguments to `PwPath I x y` unsynthesizable).
* `TangentSpace I x` is a type synonym: rewriting with `map_smul` at `f (c • x)` fails when `x` is
  given at the plain model type instead of the tangent type; the robust pattern is
  `conv_lhs => rw [← h]` followed by `rw [ContinuousLinearMap.map_smul]`, and `change` is needed to
  restate goals (`change c * (1 : ℝ) = c` for `c • 1 = c`).
-/
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.ChartConnection

namespace Submission.Length

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

/-- **The speed of a curve** at `t`: the Riemannian norm of its velocity.  (For a curve that is not
differentiable at `t` this is the norm of the junk value of `mfderiv`, which is `0`.) -/
def curveSpeed (γ : ℝ → M) (t : ℝ) : ℝ :=
  Real.sqrt (inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))

/-- **The length of a curve** over the interval `[a,b]`: the integral of the speed. -/
def curveLength (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, curveSpeed (I := I) γ t

lemma curveSpeed_def (γ : ℝ → M) (t : ℝ) :
    curveSpeed (I := I) γ t
      = Real.sqrt (inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) := rfl

lemma curveLength_def (γ : ℝ → M) (a b : ℝ) :
    curveLength (I := I) γ a b = ∫ t in a..b, curveSpeed (I := I) γ t := rfl

lemma curveSpeed_nonneg (γ : ℝ → M) (t : ℝ) : 0 ≤ curveSpeed (I := I) γ t :=
  Real.sqrt_nonneg _

lemma curveSpeed_sq (γ : ℝ → M) (t : ℝ) :
    curveSpeed (I := I) γ t ^ 2
      = inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) :=
  Real.sq_sqrt (by simpa using inner_self_nonneg (x := curveVelocity (I := I) γ t))

lemma curveSpeed_const (p : M) (t : ℝ) : curveSpeed (I := I) (fun _ : ℝ => p) t = 0 := by
  rw [curveSpeed_def, curveVelocity_const, inner_zero_left, Real.sqrt_zero]

lemma curveLength_const (p : M) (a b : ℝ) : curveLength (I := I) (fun _ : ℝ => p) a b = 0 := by
  rw [curveLength_def]
  simp only [curveSpeed_const]
  simp

lemma curveLength_nonneg (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ curveLength (I := I) γ a b := by
  rw [curveLength_def]
  exact intervalIntegral.integral_nonneg_of_forall hab fun t => curveSpeed_nonneg (I := I) γ t

lemma curveLength_self (γ : ℝ → M) (a : ℝ) : curveLength (I := I) γ a a = 0 := by
  rw [curveLength_def]; simp

lemma curveLength_neg (γ : ℝ → M) (a b : ℝ) :
    curveLength (I := I) γ a b = -curveLength (I := I) γ b a := by
  rw [curveLength_def, curveLength_def, intervalIntegral.integral_symm]

lemma curveLength_add_of_integrable (γ : ℝ → M) {a b c : ℝ}
    (hab : IntervalIntegrable (curveSpeed (I := I) γ) MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (curveSpeed (I := I) γ) MeasureTheory.volume b c) :
    curveLength (I := I) γ a b + curveLength (I := I) γ b c = curveLength (I := I) γ a c := by
  rw [curveLength_def, curveLength_def, curveLength_def]
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc

/-! ## The chart formula for the speed -/

/-- **The speed of a curve given in a chart.**  For `γ = (extChartAt I x₀).symm ∘ u` with
`u' (t) = v`, the speed is the square root of `chartGram x₀ (γ t) v v`. -/
lemma curveSpeed_chartCurve {x₀ : M} {u : ℝ → E} {t : ℝ} {v : E}
    (hu : HasDerivAt u v t) (ht : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target) :
    curveSpeed (I := I) (fun s => (extChartAt I x₀).symm (u s)) t
      = Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) v v) := by
  rw [curveSpeed_def, curveVelocity_extChartAt_symm (I := I) hu ht hstay]
  rfl

/-! ## Reparametrisation -/

/-- The velocity of an affinely reparametrised curve. -/
lemma curveVelocity_comp_mul_add {γ : ℝ → M} {c d t : ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (c * t + d)) :
    curveVelocity (I := I) (fun s : ℝ => γ (c * s + d)) t
      = c • curveVelocity (I := I) γ (c * t + d) := by
  rw [curveVelocity_apply, curveVelocity_apply]
  exact Commons.Geometry.Manifold.Tangent.mfderiv_comp_mul_add_apply γ c d t hd

/-- Reparametrisation of the speed by an orientation preserving affine map. -/
lemma curveSpeed_comp_mul_add {γ : ℝ → M} {c d t : ℝ} (hc : 0 < c)
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (c * t + d)) :
    curveSpeed (I := I) (fun s : ℝ => γ (c * s + d)) t
      = c * curveSpeed (I := I) γ (c * t + d) := by
  rw [curveSpeed_def, curveSpeed_def, curveVelocity_comp_mul_add (I := I) hd]
  have h1 : inner ℝ (c • curveVelocity (I := I) γ (c * t + d))
      (c • curveVelocity (I := I) γ (c * t + d))
      = c ^ 2 * inner ℝ (curveVelocity (I := I) γ (c * t + d))
          (curveVelocity (I := I) γ (c * t + d)) := by
    rw [inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial, sq]
    ring
  rw [h1, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq (le_of_lt hc)]

/-- **Invariance of the length under orientation preserving affine reparametrisation**, for an
interval in increasing order. -/
lemma curveLength_comp_mul_add_of_le {γ : ℝ → M} {c d a b : ℝ} (hc : 0 < c) (hab : a ≤ b)
    (hd : ∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ) I γ (c * t + d)) :
    curveLength (I := I) (fun s : ℝ => γ (c * s + d)) a b
      = curveLength (I := I) γ (c * a + d) (c * b + d) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcongr : (∫ t in a..b, curveSpeed (I := I) (fun s : ℝ => γ (c * s + d)) t)
      = ∫ t in a..b, c * curveSpeed (I := I) γ (c * t + d) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hab ?_
    intro t ht
    exact curveSpeed_comp_mul_add (I := I) hc (hd t ht)
  rw [curveLength_def, curveLength_def, hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_add (f := curveSpeed (I := I) γ) hcne d, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]

/-- **Invariance of the length under orientation preserving affine reparametrisation.** -/
lemma curveLength_comp_mul_add_of_pos {γ : ℝ → M} {c d a b : ℝ} (hc : 0 < c)
    (hd : ∀ t : ℝ, MDifferentiableAt 𝓘(ℝ) I γ (c * t + d)) :
    curveLength (I := I) (fun s : ℝ => γ (c * s + d)) a b
      = curveLength (I := I) γ (c * a + d) (c * b + d) := by
  rcases le_total a b with hab | hba
  · exact curveLength_comp_mul_add_of_le (I := I) hc hab (fun t _ => hd t)
  · have h2 : curveLength (I := I) (fun s : ℝ => γ (c * s + d)) b a
        = curveLength (I := I) γ (c * b + d) (c * a + d) :=
      curveLength_comp_mul_add_of_le (I := I) hc hba (fun t _ => hd t)
    rw [curveLength_neg (I := I) (γ := fun s : ℝ => γ (c * s + d)) a b, h2,
      curveLength_neg (I := I) (γ := γ) (c * a + d) (c * b + d)]

end

end Submission.Length
