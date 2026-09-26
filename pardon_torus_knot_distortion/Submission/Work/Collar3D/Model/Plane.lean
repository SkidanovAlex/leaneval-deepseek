import Submission.Work.Collar3D.Model.Defs

/-!
# The model collar chart of the plane along its unit circle

The chart of the collar of `Work.Collar3D.plane` along `Work.Collar3D.planeCircle`:
`ℝ³` minus the `z`-axis is homeomorphic to `S¹ × ℝ × ℝ` by

`p ↦ (unit (p 0 + p 1 · i), log ‖p 0 + p 1 · i‖, p 2)`,

the polar-coordinate chart of `ℂ ∖ {0}` crossed with the `z`-coordinate.  It carries the plane to
the middle sheet `S¹ × ℝ × {0}` and the unit circle to the core `S¹ × {0} × {0}`
(`Work.Collar3D.hasCollar_planeCircle`).
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

/-- The complement of the `z`-axis, the domain of the model collar chart. -/
def planeTube : Set R3 := {p : R3 | p 0 + p 1 * Complex.I ≠ 0}

theorem mem_planeTube (p : R3) :
    p ∈ planeTube ↔ p 0 + p 1 * Complex.I ≠ 0 := Iff.rfl

theorem planeTube_isOpen : IsOpen planeTube := by
  have h : Continuous fun p : R3 => p 0 + p 1 * Complex.I := by
    fun_prop
  exact h.isOpen_preimage {0}ᶜ isClosed_singleton.isOpen_compl

theorem norm_div_norm_self (v : ℂ) (hv : v ≠ 0) : ‖v / (‖v‖ : ℂ)‖ = 1 := by
  rw [norm_div]
  have h : ‖((‖v‖ : ℝ) : ℂ)‖ = ‖v‖ := by simp
  rw [h, div_self (norm_ne_zero_iff.mpr hv)]

theorem planeCircle_mem_planeTube (θ : ℝ) :
    planeCircle θ ∈ planeTube := by
  rw [mem_planeTube]
  have h : planeCircle θ 0 + planeCircle θ 1 * Complex.I = Complex.exp (θ * Complex.I) := by
    rw [planeCircle_zero, planeCircle_one, Complex.exp_ofReal_mul_I]
  rw [h]
  exact Complex.exp_ne_zero _

/-- The model collar chart of the plane: `p ↦ (unit (p 0 + p 1 · i), log ‖…‖, p 2)`. -/
def planeChartFun (p : planeTube) : Circle × ℝ × ℝ :=
  (⟨(p.1 0 + p.1 1 * Complex.I) / ‖p.1 0 + p.1 1 * Complex.I‖, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_div_norm_self (p.1 0 + p.1 1 * Complex.I) (p.2)⟩,
   Real.log ‖p.1 0 + p.1 1 * Complex.I‖, p.1 2)

@[simp] theorem planeChartFun_fst (p : planeTube) :
    ((planeChartFun p).1 : ℂ) = (p.1 0 + p.1 1 * Complex.I) / ‖p.1 0 + p.1 1 * Complex.I‖ :=
  rfl

@[simp] theorem planeChartFun_snd (p : planeTube) : (planeChartFun p).2.1
    = Real.log ‖p.1 0 + p.1 1 * Complex.I‖ := rfl

@[simp] theorem planeChartFun_thd (p : planeTube) : (planeChartFun p).2.2 = p.1 2 := rfl

end

end Work.Collar3D
