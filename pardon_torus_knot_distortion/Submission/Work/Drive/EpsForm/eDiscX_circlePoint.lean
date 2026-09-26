import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign2
import Submission.Work.Drive.EpsForm.WaypointDiscDefs

namespace Work.Drive.EpsForm

noncomputable section

/-- On the boundary level `s = 1` the corrected profile sits at the point
`W5c t = (cos t, sin t)` of the unit circle, so `eFunX t 1` is the point of the standard
torus of revolution with parameters `(t, t)`. -/
theorem eFunX_one_eq_torusMap (t : ℝ) : eFunX t 1 = Work.Core.torusMap t t := by
  refine WithLp.ofLp_injective 2 (funext fun i => ?_)
  fin_cases i
  · show eFunX t 1 (0 : Fin 3) = Work.Core.torusMap t t (0 : Fin 3)
    simp [eFunX_apply_zero, profX_one, Work.Core.torusMap_apply_zero, W5c]
  · show eFunX t 1 (1 : Fin 3) = Work.Core.torusMap t t (1 : Fin 3)
    simp [eFunX_apply_one, profX_one, Work.Core.torusMap_apply_one, W5c]
  · show eFunX t 1 (2 : Fin 3) = Work.Core.torusMap t t (2 : Fin 3)
    simp [eFunX_apply_two, profX_one, Work.Core.torusMap_apply_two, W5c]

/-- Reducing the angle modulo `2π` does not move the diagonal point `torusMap t t`
of the standard torus. -/
theorem torusMap_diag_toIocMod (θ : ℝ) :
    Work.Core.torusMap (toIocMod Real.two_pi_pos (-Real.pi) θ)
        (toIocMod Real.two_pi_pos (-Real.pi) θ) = Work.Core.torusMap θ θ := by
  obtain ⟨k, hk⟩ := ((toIocMod_eq_iff Real.two_pi_pos (a := -Real.pi) (b := θ)
    (c := toIocMod Real.two_pi_pos (-Real.pi) θ)).mp rfl).2
  have hk' : toIocMod Real.two_pi_pos (-Real.pi) θ = θ + (-k : ℤ) * (2 * Real.pi) := by
    have h := hk
    rw [zsmul_eq_mul] at h
    push_cast at h ⊢
    linarith
  exact (Work.Core.torusMap_eq_iff _ _ _ _).mpr ⟨⟨-k, hk'⟩, ⟨-k, hk'⟩⟩

/-- **The boundary circle of the corrected disc maps to the standard `(1,1)` curve.**
For every `θ : ℝ`, `eDiscX (circlePoint θ) = standardCurve 1 1 θ = torusMap θ θ`.

Route: `circlePoint θ` is `exp (iθ)`, whose norm is `1`, so
`eDiscX (circlePoint θ) = eFunX (arg (exp (iθ))) 1`; `eFunX t 1` is the point of `ℝ³`
with tube coordinates `profX t 1 = W5c t`, i.e. `torusMap t t`.  Finally
`Complex.arg_exp_mul_I` gives `arg (exp (iθ)) = toIocMod 2π (-π) θ`, which differs from
`θ` by a multiple of `2π`, and `torusMap` is `2π`-periodic in both variables
(`Work.Core.torusMap_eq_iff`). -/
theorem eDiscX_circlePoint (θ : ℝ) :
    eDiscX (Work.CoreTopology.circlePoint θ) = (Work.CoreTopology.standardCurve 1 1).γ θ := by
  have hnorm :
      ‖((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 := by
    rw [Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  have harg :
      Complex.arg ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ) =
        toIocMod Real.two_pi_pos (-Real.pi) θ := by
    rw [Work.CoreTopology.circlePoint_coe, Complex.arg_exp_mul_I]
  have hdisc : eDiscX (Work.CoreTopology.circlePoint θ) =
      eFunX (toIocMod Real.two_pi_pos (-Real.pi) θ) 1 := by
    rw [eDiscX, harg, hnorm]
  have hstd : (Work.CoreTopology.standardCurve 1 1).γ θ = Work.Core.torusMap θ θ := by
    rw [show (Work.CoreTopology.standardCurve 1 1).γ θ
        = (Work.CoreTopology.standardCurve 1 1) θ from rfl,
      Work.CoreTopology.standardCurve_apply, Work.Core.standardTorusCurve_eq_torusMap]
    simp
  rw [hdisc, eFunX_one_eq_torusMap, hstd, torusMap_diag_toIocMod]

end

end Work.Drive.EpsForm
