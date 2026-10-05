import Mathlib
import Submission.Work.RPB1a.Caratheodory.ReflDefs

/-!
# Holomorphy of the circle reflection off the unit circle

The reflection `diskReflect f a` of `f - a` in the unit circle is holomorphic wherever it is
defined *off* the unit circle, as soon as `f` is holomorphic on the open unit disc `ball 0 1`:

* inside the disc it agrees with `z ↦ f z - a`, which is holomorphic because `f` is;
* outside the disc it agrees with the exterior formula
  `diskReflectOuter f a z = conj (f (1 / conj z)) - conj a`, which is holomorphic because it is
  the Schwarz reflection `conj ∘ g ∘ conj` of the holomorphic function `g w = f (1 / w)` (see
  `Mathlib.Analysis.Calculus.Deriv.Star`, `differentiableAt_conj_conj_iff`).

Since the two regions `{‖z‖ < 1}` and `{1 < ‖z‖}` are open and cover the complement of the unit
circle, `diskReflect f a` is differentiable on any set avoiding the unit circle.  This is exactly
what the Painlevé-style removability argument in
`Submission.Work.RPB1a.differentiableOn_of_compl_sphere` consumes.
-/

namespace Work.RPB1a.Caratheodory

open Complex Set Metric
open scoped ContDiff Real Topology ComplexConjugate

/-- **The exterior formula is holomorphic outside the unit circle.**  If `f` is holomorphic on
the open unit disc and `1 < ‖z‖`, then `w ↦ conj (f (1 / conj w)) - conj a` is complex
differentiable at `z`.

This is Schwarz reflection: with `g w = f (1 / w)` holomorphic at `conj z` (because
`‖1 / conj z‖ = 1 / ‖z‖ < 1`), the function `conj ∘ g ∘ conj` is holomorphic at `z`
(`differentiableAt_conj_conj_iff`). -/
lemma differentiableAt_diskReflectOuter {f : ℂ → ℂ} (a : ℂ) {z : ℂ} (hz : 1 < ‖z‖)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1)) :
    DifferentiableAt ℂ (diskReflectOuter f a) z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    linarith
  have hcz0 : conj z ≠ 0 := fun h => hz0 (by simpa using congrArg conj h)
  have hmem : (1 / conj z) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, one_div, norm_inv, Complex.norm_conj]
    rw [inv_lt_one_iff₀]
    exact Or.inr hz
  have hfd : DifferentiableAt ℂ f (1 / conj z) :=
    (hd _ hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  have hinv : DifferentiableAt ℂ (fun w : ℂ => 1 / w) (conj z) := by
    have h : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) (conj z) :=
      differentiableAt_id.inv (by simpa using hcz0)
    simpa [one_div] using h
  have hg : DifferentiableAt ℂ (fun w : ℂ => f (1 / w)) (conj z) :=
    hfd.comp (conj z) hinv
  have hcc : DifferentiableAt ℂ (conj ∘ (fun w : ℂ => f (1 / w)) ∘ conj) z :=
    (differentiableAt_conj_conj_iff (f := fun w : ℂ => f (1 / w)) (x := z)).mpr hg
  have hA : DifferentiableAt ℂ (fun x : ℂ => conj (f (1 / conj x))) z := by
    simpa [Function.comp_def, one_div] using hcc
  have hB : DifferentiableAt ℂ (fun x : ℂ => conj (f (1 / conj x)) - conj a) z :=
    hA.sub (differentiableAt_const _)
  rw [show diskReflectOuter f a = fun x : ℂ => conj (f (1 / conj x)) - conj a from rfl]
  exact hB

theorem differentiableOn_diskReflect_off_sphere {f : ℂ → ℂ} (a : ℂ) {z₀ : ℂ} {δ : ℝ}
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1)) :
    DifferentiableOn ℂ (Work.RPB1a.Caratheodory.diskReflect f a)
      (Metric.ball z₀ δ \ Metric.sphere 0 1) := by
  intro z hz
  obtain ⟨hzball, hzsphere⟩ := hz
  have hne : ‖z‖ ≠ 1 := by
    intro h
    exact hzsphere (by simpa [Metric.mem_sphere, dist_zero_right] using h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- inside the unit disc: `diskReflect f a` agrees with `z ↦ f z - a` on the whole open disc
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hlt
    have hAt : DifferentiableAt ℂ (fun y : ℂ => f y - a) z :=
      ((hd z hz1).differentiableAt (Metric.isOpen_ball.mem_nhds hz1)).sub
        (differentiableAt_const a)
    have hev : (diskReflect f a) =ᶠ[𝓝 z] (fun y : ℂ => f y - a) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz1) fun y hy => by
        rw [diskReflect_of_le_one]
        exact le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy)
    exact (hAt.congr_of_eventuallyEq hev).differentiableWithinAt
  · -- outside the unit disc: agrees with the exterior formula near `z`
    have hAtOuter : DifferentiableAt ℂ (diskReflectOuter f a) z :=
      differentiableAt_diskReflectOuter a hgt hd
    have hset : {y : ℂ | 1 < ‖y‖} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hgt
    have hev : (diskReflect f a) =ᶠ[𝓝 z] diskReflectOuter f a :=
      Filter.eventually_of_mem hset fun y hy => by
        rw [diskReflect_of_one_lt hy]
        rfl
    exact (hAtOuter.congr_of_eventuallyEq hev).differentiableWithinAt

end Work.RPB1a.Caratheodory
