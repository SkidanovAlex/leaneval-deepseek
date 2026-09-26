import Mathlib
import Submission.Work.BoxShrink.PinchOff.Rotation
import Submission.Work.BoxShrink.PinchOff.PerpBox
import Submission.Work.BoxShrink.PinchOff.Sharpening

/-!
# The trace of the cutting plane on the rotated torus contains a `(0,1)`-curve

For the rotation `ψ = rotDiffeo (1/4)` of `ℝ³` about the `x`-axis by `π`-free angle `1/4`, the
cutting plane `{y = 0}` (i.e. `PlaneTrace ψ 0 sigmaY 0`) meets the rotated torus in a union of two
embedded circles, each of winding vector `(0,1)`.  This module exhibits one of them explicitly.

In the parameter plane the pull-back of the plane coordinate is (`planeG_rotDiffeo`)

  `G(θ, φ) = cos (1/4) · (2 + cos φ) · sin θ − sin (1/4) · sin φ`,

and `G = 0` is solved by

  `sin θ = tan (1/4) · sin φ / (2 + cos φ)`.

Since `|tan (1/4)| < 1 ≤ 2 + cos φ`, the right-hand side lies in `[−1,1]` for every `φ`, so
`θ(φ) = arcsin (tan (1/4) · sin φ / (2 + cos φ))` is a continuous, `2π`-periodic function `θ`
which makes `φ ↦ ψ(torusMap (θ φ) φ)` a closed curve of the surface lying entirely in the plane
`{y = 0}`.  Its lift `φ ↦ (θ φ, φ)` advances by `0` in `θ` and by `2π` in `φ` over one period,
so its winding vector is `(0,1)`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The `θ`-coordinate of the trace -/

/-- The `θ`-coordinate solving `cos (1/4) (2 + cos φ) sin θ = sin (1/4) sin φ`:
`θ(φ) = arcsin (tan (1/4) · sin φ / (2 + cos φ))`. -/
def rotTraceTheta (φ : ℝ) : ℝ :=
  Real.arcsin (Real.tan (1/4) * Real.sin φ / (2 + Real.cos φ))

/-- `tan (1/4) < 1` (the strict monotonicity of `tan` on `(−π/2, π/2)` at `1/4 < π/4`). -/
theorem tan_quarter_lt_one : Real.tan (1/4) < 1 := by
  have h : Real.tan (1/4) < Real.tan (Real.pi / 4) :=
    Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three])
  rwa [Real.tan_pi_div_four] at h

/-- `0 ≤ tan (1/4)`. -/
theorem tan_quarter_nonneg : 0 ≤ Real.tan (1/4) :=
  Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by norm_num) (by linarith [Real.pi_gt_three])

/-- The argument of `arcsin` in `rotTraceTheta` has absolute value `< 1`. -/
theorem rotTraceTheta_arg_abs_lt_one (φ : ℝ) :
    |Real.tan (1/4) * Real.sin φ / (2 + Real.cos φ)| < 1 := by
  have hden : 0 < 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  rw [abs_div, abs_mul, abs_of_pos hden, div_lt_one hden, abs_of_nonneg tan_quarter_nonneg]
  calc Real.tan (1/4) * |Real.sin φ| ≤ Real.tan (1/4) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one φ) tan_quarter_nonneg
    _ = Real.tan (1/4) := by ring
    _ < 1 := tan_quarter_lt_one
    _ ≤ 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]

/-- The argument of `arcsin` in `rotTraceTheta` lies in `[-1,1]`. -/
theorem rotTraceTheta_arg_mem (φ : ℝ) :
    Real.tan (1/4) * Real.sin φ / (2 + Real.cos φ) ∈ Set.Icc (-1) 1 := by
  have h := rotTraceTheta_arg_abs_lt_one φ
  exact ⟨le_of_lt (lt_of_lt_of_le (by linarith [h]) (neg_abs_le _)),
    le_of_lt (lt_of_le_of_lt (le_abs_self _) h)⟩

/-- The defining property of `rotTraceTheta`: its sine is the required quotient. -/
theorem sin_rotTraceTheta (φ : ℝ) :
    Real.sin (rotTraceTheta φ) = Real.tan (1/4) * Real.sin φ / (2 + Real.cos φ) := by
  unfold rotTraceTheta
  exact Real.sin_arcsin (rotTraceTheta_arg_mem φ).1 (rotTraceTheta_arg_mem φ).2

theorem continuous_rotTraceTheta : Continuous rotTraceTheta := by
  unfold rotTraceTheta
  refine Real.continuous_arcsin.comp (Continuous.div ?_ ?_ ?_)
  · exact continuous_const.mul Real.continuous_sin
  · exact continuous_const.add Real.continuous_cos
  · intro φ; exact ne_of_gt (by linarith [Real.neg_one_le_cos φ])

theorem rotTraceTheta_periodic (φ : ℝ) : rotTraceTheta (φ + 2 * Real.pi) = rotTraceTheta φ := by
  unfold rotTraceTheta
  rw [Real.sin_add_two_pi, Real.cos_add_two_pi]

/-! ## The closed curve -/

/-- The underlying map of the trace curve: `φ ↦ ψ (torusMap (θ φ) φ)`. -/
def rotTraceFun : ℝ → R3 :=
  fun t => Work.Smooth.Morse.param (rotDiffeo (1/4)) (rotTraceTheta t, t)

theorem continuous_rotTraceFun : Continuous rotTraceFun :=
  (Work.Smooth.Morse.param_continuous (rotDiffeo (1/4))).comp
    (continuous_rotTraceTheta.prodMk continuous_id)

theorem rotTraceFun_periodic (t : ℝ) : rotTraceFun (t + 2 * Real.pi) = rotTraceFun t := by
  unfold rotTraceFun
  simp only [rotTraceTheta_periodic t]
  rw [Work.Smooth.Morse.param_apply, Work.Smooth.Morse.param_apply,
      Work.Core.torusMap_add_two_pi_right]

/-- The trace curve on the surface of the rotated torus. -/
def rotTraceCurve : Work.CoreTopology.ClosedCurve (surface (rotDiffeo (1/4))) where
  γ := rotTraceFun
  cont := continuous_rotTraceFun
  periodic := rotTraceFun_periodic
  mem := fun t => Work.Smooth.Morse.param_mem (rotDiffeo (1/4)) (rotTraceTheta t, t)

/-- The curve is the rotation of the standard torus point with parameters `(θ t, t)`. -/
theorem rotTraceFun_apply (t : ℝ) :
    rotTraceFun t = rotDiffeo (1/4) (Work.Core.torusMap (rotTraceTheta t) t) := by
  unfold rotTraceFun
  rw [Work.Smooth.Morse.param_apply]

/-- **The second coordinate of the trace curve vanishes**: the curve lies in the plane `{y = 0}`. -/
theorem rotTraceFun_coord_one (t : ℝ) : (rotTraceFun t) 1 = 0 := by
  rw [rotTraceFun_apply, rotDiffeo_apply, rotFun_coord_one,
      Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
      sin_rotTraceTheta t, Real.tan_eq_sin_div_cos]
  have hcos : Real.cos (1/4) ≠ 0 := by
    apply ne_of_gt
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have hden : 2 + Real.cos t ≠ 0 := by linarith [Real.neg_one_le_cos t]
  field_simp
  ring

/-- **The trace curve lies in the trace of the cutting plane.** -/
theorem rotTraceFun_mem_planeTrace (t : ℝ) :
    rotTraceFun t ∈ PlaneTrace (rotDiffeo (1/4)) 0 sigmaY 0 := by
  refine ⟨Work.Smooth.Morse.param_mem (rotDiffeo (1/4)) (rotTraceTheta t, t), ?_⟩
  rw [Work.BoxShrink.Core.mem_cutPlane, sigmaY_two]
  simp only [PiLp.zero_apply, zero_add]
  exact rotTraceFun_coord_one t

/-! ## The winding vector -/

/-- The lift of the trace curve to the parameter plane: `φ ↦ (θ φ, φ)`. -/
def rotTraceLift : Work.CoreTopology.LiftOf (surface (rotDiffeo (1/4))) rotTraceCurve where
  Θ := rotTraceTheta
  Φ := fun t => t
  contΘ := continuous_rotTraceTheta
  contΦ := continuous_id
  lifts := fun _ => rfl

/-- **The winding vector of the trace curve is `(0,1)`**: `θ` is periodic, while `φ` advances by
one full turn. -/
theorem rotTraceLift_winding : rotTraceLift.winding = (0, 1) := by
  have hspec := rotTraceLift.winding_spec
  have h1 : (rotTraceLift.winding).1 = 0 := by
    have hΘ : rotTraceLift.Θ (2 * Real.pi) = rotTraceLift.Θ 0 := by
      show rotTraceTheta (2 * Real.pi) = rotTraceTheta 0
      simpa using rotTraceTheta_periodic 0
    have hmul : (rotTraceLift.winding).1 * (2 * Real.pi) = 0 := by
      linarith [hspec.1, hΘ]
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h Work.CoreTopology.two_pi_ne_zero
  have h2 : (rotTraceLift.winding).2 = 1 := by
    have hΦ : rotTraceLift.Φ (2 * Real.pi) = rotTraceLift.Φ 0 + 1 * (2 * Real.pi) := by
      show 2 * Real.pi = 0 + 1 * (2 * Real.pi); ring
    have hmul : (rotTraceLift.winding).2 * (2 * Real.pi) = 1 * (2 * Real.pi) := by
      linarith [hspec.2, hΦ]
    exact_mod_cast (mul_right_cancel₀ Work.CoreTopology.two_pi_ne_zero hmul)
  exact Prod.ext h1 h2

theorem windingOf_rotTraceCurve :
    Work.SurgeryInvariance.windingOf (surface (rotDiffeo (1/4))) rotTraceCurve = (0, 1) := by
  rw [Work.SurgeryInvariance.windingOf_eq (surface (rotDiffeo (1/4))) rotTraceCurve rotTraceLift,
    rotTraceLift_winding]

/-! ## The statement -/

theorem rotation_quarter_trace_curve :
    ∃ γ : Work.CoreTopology.ClosedCurve (surface (rotDiffeo (1 / 4))),
      (∀ t : ℝ, γ t ∈ PlaneTrace (rotDiffeo (1 / 4)) 0 sigmaY 0) ∧
      Work.SurgeryInvariance.windingOf (surface (rotDiffeo (1 / 4))) γ = (0, 1) :=
  ⟨rotTraceCurve, rotTraceFun_mem_planeTrace, windingOf_rotTraceCurve⟩

end

end Work.BoxShrink.PinchOff
