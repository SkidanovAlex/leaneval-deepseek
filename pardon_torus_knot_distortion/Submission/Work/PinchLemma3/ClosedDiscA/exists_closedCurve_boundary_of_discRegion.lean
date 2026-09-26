import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.SurgeryInvariance.DiscRegion.not_isEssential
import Submission.Work.Smooth.Jordan.Defs

/-!
# The boundary circle of an embedded disc of the torus is a closed curve

`Work.SurgeryInvariance.DiscRegion P` records an embedded closed disc `D` of the surface
`F = P.carrier` of a parametrised torus: an injective continuous map `D.e` of the closed unit
disc `𝔻 ⊆ ℂ` into `F` whose interior is open in `F`.

This file proves that the *boundary circle* `D.boundary` of such a disc is the image of a closed
curve of the torus which is **simple** and **inessential**:

  `∃ γ : ClosedCurve P, Set.range γ.γ = D.boundary ∧ IsSimple P γ ∧ ¬ IsEssential P γ`.

The curve is `γ t = D.e (circlePoint t)`, the parametrisation of the boundary circle by the unit
circle of `ℂ`.  It is

* well defined and periodic, because `circlePoint` is `2π`-periodic;
* simple, because `D.e` is injective and `circlePoint` is injective on the fundamental period
  `[0, 2π)` (the exponential map `θ ↦ e^{iθ}` winds once around the circle);
* inessential, because its image lies in the disc `D`, so it is null-homotopic in `F`
  (`Work.SurgeryInvariance.DiscRegion.not_isEssential`).

The curve is the input of the collar/peeling arguments of the chapter: it is the closed curve
along which the region is cut when the boundary circle of a disc is deleted
(`Work.PinchLemma3.ClosedDiscA.windingSpan_halves_union_disc_eq_sdiff_boundary`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchLemma3.ClosedDiscA

noncomputable section

/-! ## The unit circle of `ℂ` -/

/-- `Work.CoreTopology.circlePoint` is continuous. -/
theorem continuous_circlePoint :
    Continuous (Work.CoreTopology.circlePoint : ℝ → Metric.closedBall (0 : ℂ) 1) := by
  refine Continuous.subtype_mk ?_ (fun θ => (Work.CoreTopology.circlePoint θ).2)
  show Continuous fun θ : ℝ => Complex.exp (θ * Complex.I)
  fun_prop

/-- `Work.CoreTopology.circlePoint` is `2π`-periodic. -/
theorem circlePoint_add_two_pi (θ : ℝ) :
    Work.CoreTopology.circlePoint (θ + 2 * Real.pi) = Work.CoreTopology.circlePoint θ := by
  apply Subtype.ext
  rw [Work.CoreTopology.circlePoint_coe, Work.CoreTopology.circlePoint_coe,
    show (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I from by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Every point of the unit circle of `ℂ` is `e^{iθ}` for some real `θ`. -/
theorem exists_circlePoint_eq (z : Metric.closedBall (0 : ℂ) 1) (hz : ‖(z : ℂ)‖ = 1) :
    ∃ θ : ℝ, Work.CoreTopology.circlePoint θ = z := by
  refine ⟨(z : ℂ).arg, Subtype.ext ?_⟩
  rw [Work.CoreTopology.circlePoint_coe]
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hz, Complex.ofReal_one, one_mul] at h
  exact h

/-- **The unit circle is traversed injectively over one period.**  The exponential map
`θ ↦ e^{iθ}` is injective on `[0, 2π)`. -/
theorem circlePoint_injOn :
    Set.InjOn (Work.CoreTopology.circlePoint : ℝ → Metric.closedBall (0 : ℂ) 1)
      (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  have hc : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) := by
    have h := congrArg (fun z : Metric.closedBall (0 : ℂ) 1 => (z : ℂ)) hab
    simpa only [Work.CoreTopology.circlePoint_coe] using h
  refine eq_of_circleMap_eq (c := 0) (R := 1) one_ne_zero ?_ ?_
  · rw [abs_lt]
    exact ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩
  · simpa [circleMap] using hc

/-! ## The boundary curve of an embedded disc -/

/-- **The boundary circle of an embedded disc of the torus is a simple, inessential closed
curve.**

The curve is the parametrisation `γ t = D.e (circlePoint t)` of the boundary circle of `D` by
the unit circle of `ℂ`: it is continuous and `2π`-periodic, its range is exactly `D.boundary`,
it is injective on the fundamental period `[0, 2π)` because `D.e` is injective and the
exponential map winds once around the circle, and it is inessential because it lies in the disc
`D`. -/
theorem exists_closedCurve_boundary_of_discRegion {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    ∃ γ : Work.CoreTopology.ClosedCurve P, Set.range γ.γ = D.boundary ∧
      Work.CoreTopology.IsSimple P γ ∧ ¬ Work.CoreTopology.IsEssential P γ := by
  have hcont : Continuous fun t : ℝ => D.e (Work.CoreTopology.circlePoint t) :=
    D.e.continuous.comp continuous_circlePoint
  have hper : ∀ t : ℝ, D.e (Work.CoreTopology.circlePoint (t + 2 * Real.pi)) =
      D.e (Work.CoreTopology.circlePoint t) :=
    fun t => congrArg (fun z => D.e z) (circlePoint_add_two_pi t)
  have hmem : ∀ t : ℝ, D.e (Work.CoreTopology.circlePoint t) ∈ P.carrier :=
    fun t => D.mem _
  let γ : Work.CoreTopology.ClosedCurve P :=
    { γ := fun t => D.e (Work.CoreTopology.circlePoint t)
      cont := hcont
      periodic := hper
      mem := hmem }
  have hγ : γ.γ = fun t : ℝ => D.e (Work.CoreTopology.circlePoint t) := rfl
  refine ⟨γ, ?_, ?_, ?_⟩
  · show Set.range γ.γ = D.e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1}
    rw [hγ]
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨Work.CoreTopology.circlePoint t, ?_, rfl⟩
      show ‖((Work.CoreTopology.circlePoint t : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1
      rw [Work.CoreTopology.circlePoint_coe]
      exact Complex.norm_exp_ofReal_mul_I t
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨θ, hθ⟩ := exists_circlePoint_eq z hz
      exact ⟨θ, by simp only [hθ]⟩
  · show Set.InjOn γ.γ (Set.Ico 0 (2 * Real.pi))
    rw [hγ]
    intro a ha b hb hab
    exact circlePoint_injOn ha hb (D.inj hab)
  · exact Work.SurgeryInvariance.DiscRegion.not_isEssential D γ
      (fun t => ⟨Work.CoreTopology.circlePoint t, rfl⟩)

end

end Work.PinchLemma3.ClosedDiscA
