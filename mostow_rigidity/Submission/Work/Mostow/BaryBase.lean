import Mathlib
import Submission.Mostow.Interfaces

/-!
# Base facts for the barycentre argument (area T4)

Elementary hyperboloid / chart algebra for `E n`, the Busemann function `busemann` and the
bounds used by the barycentre development.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Real

noncomputable section

variable {n : ℕ}

theorem mem_Sph_iff (ξ : E n) : ξ ∈ Sph n ↔ ‖ξ‖ = 1 := by
  rw [Sph, Metric.mem_sphere, dist_eq_norm, sub_zero]

/-! ## `tpart` -/

theorem tpart_pos (u : E n) : 0 < tpart u := by
  rw [tpart, Real.sqrt_pos]
  nlinarith [sq_nonneg ‖u‖]

theorem tpart_sq (u : E n) : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := by
  rw [tpart, Real.sq_sqrt (by nlinarith [sq_nonneg ‖u‖])]

theorem tpart_zero : tpart (0 : E n) = 1 := by
  rw [tpart, norm_zero]; norm_num

theorem continuous_tpart : Continuous (tpart : E n → ℝ) :=
  Real.continuous_sqrt.comp (by fun_prop)

theorem one_le_tpart (u : E n) : 1 ≤ tpart u := by
  rw [tpart]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg ‖u‖]

theorem norm_le_tpart (u : E n) : ‖u‖ ≤ tpart u := by
  have h : ‖u‖ ^ 2 ≤ tpart u ^ 2 := by rw [tpart_sq]; nlinarith [norm_nonneg u]
  have h' : |‖u‖| ≤ |tpart u| := sq_le_sq.mp h
  rwa [abs_of_nonneg (norm_nonneg u), abs_of_nonneg (le_of_lt (tpart_pos u))] at h'

theorem tpart_add_norm_mul_tpart_sub_norm (u : E n) :
    (tpart u + ‖u‖) * (tpart u - ‖u‖) = 1 := by
  have h := tpart_sq u; nlinarith [h]

theorem tpart_sub_norm_pos (u : E n) : 0 < tpart u - ‖u‖ := by
  have h := tpart_add_norm_mul_tpart_sub_norm u
  have h1 : 0 < tpart u + ‖u‖ := by
    have := tpart_pos u; have := norm_nonneg u; linarith
  nlinarith [h, h1]

theorem tpart_add_norm_pos (u : E n) : 0 < tpart u + ‖u‖ := by
  have h1 := tpart_pos u; have h2 := norm_nonneg u; linarith

/-! ## hyperbolic distance -/

theorem one_le_cosh_hdist (u v : E n) : 1 ≤ tpart u * tpart v - inner ℝ u v := by
  have h1 : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have h2 : 1 + ‖u‖ * ‖v‖ ≤ tpart u * tpart v := by
    have ha : tpart u * tpart v = Real.sqrt ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) := by
      rw [tpart, tpart, Real.sqrt_mul (by nlinarith [sq_nonneg ‖u‖])]
    rw [ha]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  linarith

theorem cosh_hdist (u v : E n) : Real.cosh (hdist u v) = tpart u * tpart v - inner ℝ u v := by
  rw [hdist]; exact Real.cosh_arcosh (one_le_cosh_hdist u v)

theorem cosh_hdist_pos (u v : E n) : 0 < tpart u * tpart v - inner ℝ u v := by
  have h := one_le_cosh_hdist u v; linarith

theorem hdist_nonneg (u v : E n) : 0 ≤ hdist u v := by
  rw [hdist]; exact Real.arcosh_nonneg (one_le_cosh_hdist u v)

theorem hdist_self (u : E n) : hdist u u = 0 := by
  rw [hdist]
  have h : tpart u * tpart u - inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h2 := tpart_sq u
    nlinarith
  rw [h, Real.arcosh_zero]

theorem cosh_hdist_zero (u : E n) : Real.cosh (hdist 0 u) = tpart u := by
  rw [cosh_hdist]; simp [tpart_zero]

theorem exp_cosh_add_sinh (x : ℝ) : Real.exp x = Real.cosh x + Real.sinh x := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

theorem sinh_hdist_zero (u : E n) : Real.sinh (hdist 0 u) = ‖u‖ := by
  have h1 := cosh_hdist_zero u
  have hs : Real.sinh (hdist 0 u) ^ 2 = ‖u‖ ^ 2 := by
    rw [Real.sinh_sq, h1, tpart_sq]; ring
  have h0 : 0 ≤ Real.sinh (hdist 0 u) := Real.sinh_nonneg_iff.mpr (hdist_nonneg 0 u)
  nlinarith [hs, h0, norm_nonneg u]

theorem exp_hdist_zero (u : E n) : Real.exp (hdist 0 u) = tpart u + ‖u‖ := by
  rw [exp_cosh_add_sinh, cosh_hdist_zero, sinh_hdist_zero]

theorem exp_neg_hdist_zero (u : E n) : Real.exp (-(hdist 0 u)) = tpart u - ‖u‖ := by
  rw [Real.exp_neg, exp_hdist_zero u, inv_eq_one_div, div_eq_iff (ne_of_gt (tpart_add_norm_pos u))]
  rw [mul_comm, tpart_add_norm_mul_tpart_sub_norm]

/-! ## the Busemann function -/

theorem busemann_eq_log (ξ u : E n) : busemann ξ u = Real.log (tpart u - inner ℝ u ξ) := rfl

theorem busemann_arg_pos (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) : 0 < tpart u - inner ℝ u ξ := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have h1 : inner ℝ u ξ ≤ ‖u‖ * ‖ξ‖ := real_inner_le_norm u ξ
  rw [hξn, mul_one] at h1
  have h3 : 0 < tpart u - ‖u‖ := tpart_sub_norm_pos u
  linarith

theorem exp_busemann (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) :
    Real.exp (busemann ξ u) = tpart u - inner ℝ u ξ :=
  Real.exp_log (busemann_arg_pos ξ hξ u)

theorem busemann_zero (ξ : E n) : busemann ξ (0 : E n) = 0 := by
  rw [busemann_eq_log, tpart_zero, inner_zero_left, sub_zero, Real.log_one]

theorem busemann_le_hdist_zero (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) :
    busemann ξ u ≤ hdist 0 u := by
  rw [busemann_eq_log]
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have h1 : -(‖u‖) ≤ inner ℝ u ξ := by
    have h := abs_real_inner_le_norm u ξ
    rw [hξn, mul_one] at h
    exact neg_le_of_abs_le h
  have hle : tpart u - inner ℝ u ξ ≤ tpart u + ‖u‖ := by linarith
  have hpos := busemann_arg_pos ξ hξ u
  calc Real.log (tpart u - inner ℝ u ξ) ≤ Real.log (tpart u + ‖u‖) :=
        Real.log_le_log hpos hle
    _ = hdist 0 u := by rw [← Real.log_exp (hdist 0 u), exp_hdist_zero]

theorem neg_hdist_zero_le_busemann (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) :
    -(hdist 0 u) ≤ busemann ξ u := by
  rw [busemann_eq_log]
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have h1 : inner ℝ u ξ ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u ξ
    rw [hξn, mul_one] at h
    exact le_of_abs_le h
  have hle : tpart u - ‖u‖ ≤ tpart u - inner ℝ u ξ := by linarith
  have hpos : 0 < tpart u - ‖u‖ := tpart_sub_norm_pos u
  calc -(hdist 0 u) = Real.log (tpart u - ‖u‖) := by
        rw [← Real.log_exp (-(hdist 0 u)), exp_neg_hdist_zero]
    _ ≤ Real.log (tpart u - inner ℝ u ξ) := Real.log_le_log hpos hle

theorem abs_busemann_le_hdist_zero (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) :
    |busemann ξ u| ≤ hdist 0 u :=
  abs_le.2 ⟨neg_hdist_zero_le_busemann ξ hξ u, busemann_le_hdist_zero ξ hξ u⟩

theorem measurable_busemann (u : E n) : Measurable (fun ξ : E n => busemann ξ u) := by
  have hcont : Continuous (fun ξ : E n => tpart u - inner ℝ u ξ) := by fun_prop
  have h : Measurable (fun ξ : E n => Real.log (tpart u - inner ℝ u ξ)) :=
    Real.measurable_log.comp hcont.measurable
  exact h

theorem continuousAt_busemann (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) :
    ContinuousAt (fun v : E n => busemann ξ v) u := by
  have hcont : ContinuousAt (fun v : E n => tpart v - inner ℝ v ξ) u := by
    have : Continuous (fun v : E n => tpart v - inner ℝ v ξ) := by
      have h1 : Continuous (tpart : E n → ℝ) := continuous_tpart
      fun_prop
    exact this.continuousAt
  exact hcont.log (ne_of_gt (busemann_arg_pos ξ hξ u))

/-- the midpoint of `y` and `z` in the chart (junk for `y = z`) -/
def hmid (y z : E n) : E n := (2 * Real.cosh (hdist y z / 2))⁻¹ • (y + z)

/-- the point at distance `t` from `0` on the ray towards `ξ` -/
def hray (ξ : E n) (t : ℝ) : E n := Real.sinh t • ξ

end

end Work.Mostow
