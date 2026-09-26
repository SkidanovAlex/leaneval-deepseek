import Mathlib
import Submission.Work.Collar3D.Model.Plane

namespace Work.Collar3D.Model

/-!
# The model collar chart of the plane is a homeomorphism

This file proves `Work.Collar3D.Model.planeChartHomeo`: the chart
`p ↦ (unit (p 0 + p 1 · i), log ‖p 0 + p 1 · i‖, p 2)` of the complement of the `z`-axis is a
homeomorphism onto `S¹ × ℝ × ℝ`, with inverse `(w, s, t) ↦ (e^s · w.re, e^s · w.im, t)`.

The inverse is written down explicitly (`planeChartInv`), shown to land in the complement of the
`z`-axis and to be continuous (`planeChartInv_mem`, `continuous_planeChartInv`), and the two
compositions with `planeChartFun` are computed (`planeChartFun_planeChartInv`,
`planeChartInv_planeChartFun`).  The forward map is continuous as well
(`continuous_planeChartFun`), and the homeomorphism is assembled from the resulting `Equiv`.
-/

noncomputable section

open Classical

/-- The inverse of the model collar chart of the plane, as a map into `ℝ³`:
`(w, s, t) ↦ (e^s · Re w, e^s · Im w, t)`. -/
def planeChartInv (q : Circle × ℝ × ℝ) : R3 :=
  WithLp.toLp 2 ![Real.exp q.2.1 * (q.1 : ℂ).re, Real.exp q.2.1 * (q.1 : ℂ).im, q.2.2]

@[simp] theorem planeChartInv_zero (q : Circle × ℝ × ℝ) :
    planeChartInv q 0 = Real.exp q.2.1 * (q.1 : ℂ).re := rfl

@[simp] theorem planeChartInv_one (q : Circle × ℝ × ℝ) :
    planeChartInv q 1 = Real.exp q.2.1 * (q.1 : ℂ).im := rfl

@[simp] theorem planeChartInv_two (q : Circle × ℝ × ℝ) : planeChartInv q 2 = q.2.2 := rfl

/-- A point of the circle `S¹` has norm one and in particular is nonzero. -/
theorem circle_coe_norm (w : Circle) : ‖(w : ℂ)‖ = 1 := by
  have := w.2
  rwa [Metric.mem_sphere, dist_zero_right] at this

/-- The complex number attached to a point of the plane tube is nonzero. -/
theorem planeChartFun_ne_zero (p : planeTube) : p.1 0 + p.1 1 * Complex.I ≠ 0 :=
  (mem_planeTube p.1).mp p.2

/-- The complex number attached to `planeChartInv q` is `e^s · w`; note the first two coordinates
of `planeChartInv q` are exactly its real and imaginary parts. -/
theorem planeChartInv_sum (q : Circle × ℝ × ℝ) :
    planeChartInv q 0 + planeChartInv q 1 * Complex.I = (Real.exp q.2.1 : ℂ) * (q.1 : ℂ) := by
  apply Complex.ext <;>
    simp [planeChartInv_zero, planeChartInv_one, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im]

/-- The inverse chart lands in the complement of the `z`-axis. -/
theorem planeChartInv_mem (q : Circle × ℝ × ℝ) : planeChartInv q ∈ planeTube := by
  rw [mem_planeTube, planeChartInv_sum]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    (norm_ne_zero_iff.mp (by rw [circle_coe_norm q.1]; norm_num))

/-- The modulus of the complex number attached to `planeChartInv (w, s, t)` is `e^s`. -/
theorem planeChartInv_norm (q : Circle × ℝ × ℝ) :
    ‖planeChartInv q 0 + planeChartInv q 1 * Complex.I‖ = Real.exp q.2.1 := by
  rw [planeChartInv_sum, Complex.norm_mul, circle_coe_norm, mul_one]
  simp

/-- The inverse chart is continuous. -/
theorem continuous_planeChartInv : Continuous planeChartInv := by
  unfold planeChartInv
  apply (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The model collar chart of the plane is continuous. -/
theorem continuous_planeChartFun : Continuous planeChartFun := by
  have hnum : Continuous fun p : planeTube => p.1 0 + p.1 1 * Complex.I := by fun_prop
  have hnormR : Continuous fun p : planeTube => ‖p.1 0 + p.1 1 * Complex.I‖ := hnum.norm
  have hnorm : Continuous fun p : planeTube => ((‖p.1 0 + p.1 1 * Complex.I‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hnormR
  have hdiv : Continuous fun p : planeTube =>
      (p.1 0 + p.1 1 * Complex.I) / ((‖p.1 0 + p.1 1 * Complex.I‖ : ℝ) : ℂ) :=
    hnum.div hnorm (fun p => by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact norm_ne_zero_iff.mpr (planeChartFun_ne_zero p))
  have h3 : Continuous fun p : planeTube => p.1 2 := by fun_prop
  refine Continuous.prodMk ?_ ?_
  · exact hdiv.subtype_mk (fun p => by
      rw [Metric.mem_sphere, dist_zero_right]
      exact norm_div_norm_self _ (planeChartFun_ne_zero p))
  · exact Continuous.prodMk (hnormR.log (fun p => by
      rw [norm_ne_zero_iff]; exact planeChartFun_ne_zero p)) h3

/-- `planeChartFun` is a right inverse of `planeChartInv`: the chart is onto `S¹ × ℝ × ℝ`. -/
theorem planeChartFun_planeChartInv (q : Circle × ℝ × ℝ) :
    planeChartFun ⟨planeChartInv q, planeChartInv_mem q⟩ = q := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · simp only [planeChartFun_fst]
    rw [planeChartInv_norm, planeChartInv_sum]
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  · simp only [planeChartFun_snd]
    rw [planeChartInv_norm, Real.log_exp]
  · simp only [planeChartFun_thd, planeChartInv_two]

/-- `planeChartFun` is a left inverse of `planeChartInv`: the chart is injective. -/
theorem planeChartInv_planeChartFun (p : planeTube) : planeChartInv (planeChartFun p) = p.1 := by
  have hz : p.1 0 + p.1 1 * Complex.I ≠ 0 := planeChartFun_ne_zero p
  rw [WithLp.ext_iff]
  funext i
  fin_cases i <;> simp [planeChartInv, planeChartFun_snd, planeChartFun_fst] <;>
    rw [Real.exp_log (norm_pos_iff.mpr hz), mul_comm,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

/-- The inverse chart, as a map into the complement of the `z`-axis. -/
def planeChartInvFun (q : Circle × ℝ × ℝ) : planeTube :=
  ⟨planeChartInv q, planeChartInv_mem q⟩

/-- The inverse chart is continuous as a map into the complement of the `z`-axis. -/
theorem continuous_planeChartInvFun : Continuous planeChartInvFun :=
  continuous_planeChartInv.subtype_mk planeChartInv_mem

/-- **The model collar chart of the plane is a homeomorphism.**  The map
`p ↦ (unit (p 0 + p 1 · i), log ‖p 0 + p 1 · i‖, p 2)` of the complement of the `z`-axis onto
`S¹ × ℝ × ℝ` is a homeomorphism; its inverse is `(w, s, t) ↦ (e^s · w.re, e^s · w.im, t)`. -/
theorem planeChartHomeo :
    ∃ Φ : planeTube ≃ₜ Circle × ℝ × ℝ, ∀ p : planeTube, Φ p = planeChartFun p := by
  refine ⟨Homeomorph.mk (Equiv.mk planeChartFun planeChartInvFun ?_ ?_) continuous_planeChartFun
    continuous_planeChartInvFun, fun p => rfl⟩
  · intro p
    exact Subtype.ext (planeChartInv_planeChartFun p)
  · intro q
    exact planeChartFun_planeChartInv q

end

end Work.Collar3D.Model
